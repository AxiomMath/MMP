module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Singularities.PltFloorNormal
import MMP.AlgebraicGeometry.Singularities.DltAmplePerturbation
import MMP.AlgebraicGeometry.Singularities.DltDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso

/-!
# The components of the round down of a dlt pair are normal

Let `(X, Δ)` be a dlt pair of dimension `n ≥ 2` with `Δ` effective, over an algebraically closed
field of characteristic zero, and let `S` be a prime divisor with coefficient `1` in `Δ`.
Normality of `S` is local. Let `U` be an affine open of `X` meeting `S`. Then `(U, Δ|_U)` is dlt,
`U` is quasi-projective and `0` is an ample Cartier divisor on `U`, so perturbing `Δ|_U` by
`Δ₁ = (Δ - S)|_U` gives a divisor `D` with no component in common with `Δ` and a dlt boundary
`Θ = Δ|_U - εΔ₁ + εD` for small `ε > 0`. Its round down is `S ∩ U`, which is irreducible, so
`(U, Θ)` is plt and `S ∩ U = ⌊Θ⌋` is normal by `MMP.Mori.IsDltPair.isNormal_suppScheme_roundDown`.

## Main results

* `MMP.Mori.IsDltPair.isNormal_subscheme_of_coeff_roundDown_ne_zero`: every prime divisor
  occurring in `⌊Δ⌋` is normal, with its reduced scheme structure.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 5.52
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

/-! ### Normality is local -/

/-- A scheme each of whose points lies in the image of an open immersion from a normal scheme is
normal. -/
private theorem isNormal_of_forall_mem_range {S : Scheme.{u}}
    (h : ∀ z : S, ∃ (T : Scheme.{u}) (j : T ⟶ S), IsOpenImmersion j ∧ IsNormal T ∧
      z ∈ Set.range j) : IsNormal S := by
  refine (isNormal_iff_stalk_normal S).mpr fun z => ?_
  obtain ⟨T, j, hj, hT, t, rfl⟩ := h z
  let e : S.presheaf.stalk (j t) ≃+* T.presheaf.stalk t :=
    MMP.Threefold.Mori.OpenRestriction.stalkEquivOfOpenImmersion j t
  haveI := hT.stalk_normal t
  exact ⟨e.symm.toMulEquiv.isDomain_iff.mp inferInstance, IsIntegrallyClosed.of_equiv e.symm⟩

/-! ### Restricting a dlt pair to an open subscheme -/

/-- Composing restriction maps of prime divisors along open immersions. -/
private theorem primeDivisorMap_comp {W V X : Scheme.{u}} (a : W ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b] (E : MMP.Mori.PrimeDivisor W) :
    OpenWeilRestriction.primeDivisorMap (a ≫ b) E =
      OpenWeilRestriction.primeDivisorMap b (OpenWeilRestriction.primeDivisorMap a E) := by
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  simp only [OpenWeilRestriction.genericPoint_primeDivisorMap, Scheme.Hom.comp_base,
    TopCat.comp_app]

/-- Restriction maps of prime divisors along equal open immersions agree. -/
private theorem primeDivisorMap_congr {V X : Scheme.{u}} {a b : V ⟶ X} (h : a = b)
    [IsOpenImmersion a] [IsOpenImmersion b] (E : MMP.Mori.PrimeDivisor V) :
    OpenWeilRestriction.primeDivisorMap a E = OpenWeilRestriction.primeDivisorMap b E := by
  subst h
  rfl

/-- An snc divisor stays snc after pulling it back along an open immersion. -/
private theorem isSNC_comapDomain {R : Type*} [Zero R] {W X Y : Scheme.{u}} (j : W ⟶ X)
    [IsOpenImmersion j] (g : X ⟶ Y)
    [∀ E : MMP.Mori.PrimeDivisor X, LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ g)]
    {D : DivisorWithCoeffs R X} (hD : D.IsSNC g) :
    DivisorWithCoeffs.IsSNC (j ≫ g)
      (Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j) D
        (OpenWeilRestriction.primeDivisorMap_injective j).injOn : DivisorWithCoeffs R W) := by
  refine ⟨fun E hE => ?_, fun w => ?_⟩
  · have hE' : OpenWeilRestriction.primeDivisorMap j E ∈ D.support := by
      simpa [Finsupp.mem_support_iff] using hE
    have hsm := hD.1 _ hE'
    refine (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff j g
      (OpenWeilRestriction.primeDivisorMap j E).idealSheaf E.idealSheaf
      (MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap j E)).mpr ?_
    intro z _
    rw [IsSmoothScheme, smoothLocus_eq_smoothLocus] at hsm
    rw [hsm]
    trivial
  · exact (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff j D w).mpr (hD.2 (j w))

section Helpers

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- A birational morphism from an irreducible scheme to an open subscheme `U` of the integral
scheme `X` is birational as a morphism to `X`. -/
private theorem isBirationalMorphism_comp_ι {Y : Scheme.{u}} [IrreducibleSpace Y]
    (U : X.Opens) {g : Y ⟶ U} (hg : IsBirationalMorphism g) : IsBirationalMorphism (g ≫ U.ι) := by
  have : Nonempty Y := (IrreducibleSpace.isIrreducible_univ Y).nonempty.to_subtype.map Subtype.val
  obtain ⟨W, hWne, hW⟩ := hg.exists_isOpenImmersion
  have : Nonempty W := hWne.to_subtype
  have hd : Dense (((W.ι ≫ g) ≫ U.ι).opensRange : Set X) :=
    ((W.ι ≫ g) ≫ U.ι).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  refine ⟨⟨W, W.isOpen.dense hWne, _, hd, ((W.ι ≫ g) ≫ U.ι).isoOpensRange⟩, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨W, W.isOpen.dense hWne, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, Scheme.Hom.isoOpensRange_hom_ι, Scheme.topIso_hom,
    Category.assoc]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans (Scheme.homOfLE_ι_assoc _ _ _).symm

/-- A divisor `(Y, f, E)` over a nonempty open `U ⊆ X` with discrepancy `a` over `(U, Δ|_U)` gives
a divisor `D₁ = (Y, f ≫ ι_U, E)` over `X` with `D₁.f η_E = ι_U (f η_E)`, whose discrepancy over
`(X, Δ)` is `a`. -/
public theorem exists_isDiscrepancy_of_restrictOpen [PerfectField k] (h : IsPairWith sX n K Δ)
    (U : X.Opens) [Nonempty U] {D : DivisorOver k (U.ι ≫ sX)} {a : ℚ}
    (ha : IsDiscrepancy (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U) D a) :
    ∃ D₁ : DivisorOver k sX, D₁.f D₁.E.genericPoint = U.ι (D.f D.E.genericPoint) ∧
      IsDiscrepancy sX n K Δ D₁ a := by
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨_, (Classical.arbitrary U).2⟩)
  have := D.isIntegral
  let D₁ : DivisorOver k sX := ⟨D.Y, D.f ≫ U.ι, by rw [Category.assoc]; exact D.isNormalVariety,
    isBirationalMorphism_comp_ι U D.isBirationalMorphism, D.E⟩
  have hcen : ((D₁.center : Set X) ∩ U).Nonempty :=
    ⟨_, by rw [D₁.center_eq_closure_genericPoint]; exact subset_closure rfl,
      (D.f D.E.genericPoint).2⟩
  obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy h.isPair h.2.1 D₁
  obtain ⟨hY, hf, E', -, hval, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff h D₁ U hcen
  have hv : (⟨_, D₁.f ∣_ U, hY, hf, E'⟩ : DivisorOver k (U.ι ≫ sX)).valuation = D.valuation := by
    have := D.isNormal
    have := D.isLocallyNoetherian
    have := D.isDominant
    ext t
    obtain ⟨s, rfl⟩ :=
      (functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤ ⟨Classical.arbitrary U, trivial⟩).2 t
    refine (congrArg (· s) hval).symm.trans ?_
    change D.E.divisorialValuation (functionFieldMap (D.f ≫ U.ι) s) =
      D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap U.ι s))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  have hba := MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hv
    (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq (h.restrictOpen U).1 hv)
    ((hiff b).1 hb) ha
  exact ⟨D₁, rfl, hba ▸ hb⟩

/-- The restriction of a dlt pair to a nonempty open subscheme is dlt. -/
public theorem IsDltPair.restrictOpen [PerfectField k] (h : IsDltPair sX n K Δ) (U : X.Opens)
    [Nonempty U] : IsDltPair (U.ι ≫ sX) n (K.restrictOpen U) (Δ.restrictOpen U) := by
  obtain ⟨hpair, hcoeff, V, hVsm, hVsnc, hZ⟩ := h
  haveI : LocallyOfFiniteType sX := hpair.1.1.toLocallyOfFiniteType
  refine ⟨hpair.restrictOpen U, fun W => hcoeff _, U.ι ⁻¹ᵁ V, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : U.ι x ∈ smoothLocus sX := hVsm hx
    rw [smoothLocus_eq_smoothLocus] at hx' ⊢
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    exact hx'
  · have hr : Set.range ((U.ι ⁻¹ᵁ V).ι ≫ U.ι) ⊆ Set.range V.ι := by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact w.2
    let j : (U.ι ⁻¹ᵁ V).toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι _ hr
    have hj : j ≫ V.ι = (U.ι ⁻¹ᵁ V).ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
    haveI : IsOpenImmersion j := IsOpenImmersion.of_comp j V.ι
    have hD : (Δ.restrictOpen U).restrictOpen (U.ι ⁻¹ᵁ V) =
        Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j) (Δ.restrictOpen V)
          (OpenWeilRestriction.primeDivisorMap_injective j).injOn := by
      ext W
      change Δ (OpenWeilRestriction.primeDivisorMap U.ι
          (OpenWeilRestriction.primeDivisorMap (U.ι ⁻¹ᵁ V).ι W)) =
        Δ (OpenWeilRestriction.primeDivisorMap V.ι (OpenWeilRestriction.primeDivisorMap j W))
      rw [← primeDivisorMap_comp, ← primeDivisorMap_comp, primeDivisorMap_congr hj]
    rw [hD, ← Category.assoc, ← hj, Category.assoc]
    exact isSNC_comapDomain j (V.ι ≫ sX) hVsnc
  · intro D a hD ha
    obtain ⟨D₁, hη, hD₁⟩ := exists_isDiscrepancy_of_restrictOpen hpair U ha
    refine hZ D₁ a ?_ hD₁
    rw [D₁.center_eq_closure_genericPoint]
    refine closure_minimal ?_ V.isOpen.isClosed_compl
    rintro _ rfl
    rw [hη]
    exact hD (by rw [D.center_eq_closure_genericPoint]; exact subset_closure rfl)

/-! ### Affine opens -/

/-- An affine scheme of finite type over a field is quasi-projective. -/
public theorem isQuasiProjective_of_isAffine {Y : Scheme.{u}} [IsAffine Y] (s : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType s] : IsQuasiProjective s :=
  ⟨⟨inferInstance, inferInstance⟩, Stacks.Ample.unitModule Y, inferInstance,
    Stacks.AmplePullback.isRelativelyAmple_of_isQuasiAffineHom_of_iso_unitModule s _ (Iso.refl _)⟩

/-- On an affine scheme the zero divisor is ample. -/
private theorem isAmple_zero {Y : Scheme.{u}} [IsAffine Y] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] : Divisor.IsAmple (0 : Divisor Y) Divisor.isCartier_zero := by
  haveI := (Divisor.isCartier_zero (X := Y)).isInvertibleModule_divisorialSheaf
  exact (Stacks.RelativeAmple.isQuasiAffine_iff_isAmple_of_iso_unitModule Y _
    Divisor.divisorialSheafZeroIso).mp inferInstance

/-! ### Isolating one component of the round down -/

/-- **Perturbing a dlt pair so that its round down is a single component.** On an affine dlt pair
`(X, Δ)` of dimension `n ≥ 2` over an algebraically closed field of characteristic zero, a prime
divisor `P` with coefficient `1` in `Δ` is the round down of some effective dlt boundary `Θ`. -/
private theorem exists_isDltPair_roundDown_eq_single [IsAffine X] [IsAlgClosed k] [CharZero k]
    (h : IsDltPair sX n K Δ) (hn : 2 ≤ n) (P : MMP.Mori.PrimeDivisor X) (hP : Δ.coeff P = 1) :
    ∃ Θ : QDivisor X, 0 ≤ Θ ∧ IsDltPair sX n K Θ ∧ Θ.roundDown = Finsupp.single P 1 := by
  haveI : LocallyOfFiniteType sX := h.1.1.1.toLocallyOfFiniteType
  set Δ₁ : QDivisor X := Δ - Finsupp.single P 1 with hΔ₁
  have hΔ₁P : Δ₁.coeff P = 0 := by
    rw [hΔ₁, DivisorWithCoeffs.coeff_sub, hP, DivisorWithCoeffs.coeff_single_self, sub_self]
  have hΔ₁W : ∀ W, W ≠ P → Δ₁.coeff W = Δ.coeff W := fun W hW => by
    rw [hΔ₁, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hW),
      sub_zero]
  obtain ⟨c, -, D, hDeff, hDΔ, -, ε₀, hε₀, hε⟩ :=
    h.exists_forall_isDltPair_sub_smul_add_smul_of_disjoint (isQuasiProjective_of_isAffine _) hn
      Divisor.isCartier_zero isAmple_zero
      (fun W => by
        by_cases hW : W = P
        · rw [hW, hΔ₁P]
        · rw [hΔ₁W W hW]
          exact (h.2.1 W).1)
      (fun W => by
        rw [hΔ₁, sub_sub_cancel]
        exact Finsupp.single_nonneg.mpr zero_le_one W)
  have hD0 : ∀ W, Δ.coeff W ≠ 0 → D.coeff W = 0 := fun W hW => by
    by_contra hne
    exact Finset.disjoint_left.mp hDΔ (Finsupp.mem_support_iff.mpr hne)
      (Finsupp.mem_support_iff.mpr hW)
  have hd₁ := hε (ε₀ / 2) (by positivity) (by linarith)
  have hd := hε (ε₀ / 4) (by positivity) (by linarith)
  refine ⟨_, fun W => (hd.2.1 W).1, hd, DivisorWithCoeffs.ext' fun W => ?_⟩
  have hb₁ := (hd₁.2.1 W).2
  have hb := (hd.2.1 W).1
  have ha := h.2.1 W
  have hDW := hDeff W
  simp only [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_add,
    DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at hb₁ hb ⊢
  by_cases hW : W = P
  · subst hW
    rw [hD0 W (by norm_num [hP]), hP, hΔ₁P, DivisorWithCoeffs.coeff_single_self]
    norm_num
  · rw [hΔ₁W W hW] at hb₁ hb ⊢
    rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hW), Int.floor_eq_zero_iff]
    by_cases hΔW : Δ.coeff W = 0
    · rw [hΔW] at hb₁ hb ⊢
      constructor <;> nlinarith
    · rw [hD0 W hΔW] at hb ⊢
      exact ⟨hb, by nlinarith [ha.2, lt_of_le_of_ne ha.1 (Ne.symm hΔW)]⟩

/-! ### The main result -/

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- The support ideal of a prime divisor with multiplicity `1` is its ideal sheaf. -/
private theorem suppIdeal_single_one (P : MMP.Mori.PrimeDivisor X) :
    DivisorWithCoeffs.suppIdeal (Finsupp.single P 1 : Divisor X) = P.idealSheaf := by
  have hsupp : DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor X) =
      Closeds.closure {P.genericPoint} := by
    apply Closeds.ext
    rw [DivisorWithCoeffs.coe_supp, Closeds.coe_closure,
      Finsupp.support_single_ne_zero _ one_ne_zero]
    simpa using AlgebraicGeometry.PrimeDivisor.support_eq_closure P
  rw [DivisorWithCoeffs.suppIdeal, hsupp]
  exact Stacks.Chow.integralComponentAt_genericPointOf P.idealSheaf P.integral

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- The prime divisor of `U` cut out by `P` on an open `U` meeting `P`, with its reduced
structure, is an open subscheme of `P`. -/
private theorem exists_openImmersion_subscheme (U : X.Opens) (P : MMP.Mori.PrimeDivisor X)
    (P' : MMP.Mori.PrimeDivisor U.toScheme) (hP' : OpenWeilRestriction.primeDivisorMap U.ι P' = P)
    (z : P.idealSheaf.subscheme) (hz : P.idealSheaf.subschemeι z ∈ U) :
    ∃ j : P'.idealSheaf.subscheme ⟶ P.idealSheaf.subscheme, IsOpenImmersion j ∧
      z ∈ Set.range j := by
  have hI : P.idealSheaf.comap U.ι = P'.idealSheaf := by
    rw [← hP']
    exact MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap U.ι P'
  have h := MMP.Threefold.Mori.OpenRestriction.exists_openImmersion_comap_subscheme U.ι P.idealSheaf
  rw [hI] at h
  obtain ⟨j, hj, -, hrange⟩ := h
  exact ⟨j, hj, hrange z (by rw [Scheme.Opens.range_ι]; exact hz)⟩

end Helpers

section Main

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}

/-- **The components of the round down of a dlt pair are normal.** Let `(X, Δ)` be a dlt pair
with canonical divisor `K` of dimension `n ≥ 2` over an algebraically closed field of
characteristic zero, with `Δ` effective. Then every prime divisor `P` occurring in `⌊Δ⌋` is
normal, with its reduced scheme structure. -/
@[mmp "prop_km5b_dlt_floor_components_normal"]
public theorem IsDltPair.isNormal_subscheme_of_coeff_roundDown_ne_zero [IsAlgClosed k]
    [CharZero k] (h : IsDltPair sX n K Δ) (hn : 2 ≤ n) (hΔ : 0 ≤ Δ) (P : PrimeDivisor X)
    (hP : Δ.roundDown.coeff P ≠ 0) :
    IsNormal P.idealSheaf.subscheme := by
  have hP1 : Δ.coeff P = 1 := by
    obtain ⟨h0, h1⟩ := h.2.1 P
    rw [DivisorWithCoeffs.coeff_roundDown] at hP
    by_contra hne
    exact hP (Int.floor_eq_zero_iff.mpr ⟨h0, lt_of_le_of_ne h1 hne⟩)
  refine isNormal_of_forall_mem_range fun z => ?_
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := P.idealSheaf.subschemeι z) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI : IsAffine U := hU
  obtain ⟨P', hP'⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    U.ι P ⟨_, hxU⟩ (by
      simpa [Scheme.IdealSheafData.range_subschemeι] using
        Set.mem_range_self (f := P.idealSheaf.subschemeι) z)
  obtain ⟨Θ, hΘ0, hΘ, hfloor⟩ := exists_isDltPair_roundDown_eq_single
    (h.restrictOpen U) hn P' (by rw [DivisorWithCoeffs.coeff_restrictOpen, hP', hP1])
  have hnorm := hΘ.isNormal_suppScheme_roundDown (hΘ.isPltPair_of_pairwise_disjoint hn hΘ0 <| by
    rw [hfloor]
    refine (Set.subsingleton_singleton (a := P').anti fun W hW => ?_).pairwise _
    by_contra hne
    exact hW (DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hne) _)) hn hΘ0
  rw [hfloor, DivisorWithCoeffs.suppScheme, suppIdeal_single_one] at hnorm
  obtain ⟨j, hj, hz⟩ := exists_openImmersion_subscheme U P P' hP' z hxU
  exact ⟨_, j, hj, hnorm, hz⟩

end Main

end MMP.Mori

end
