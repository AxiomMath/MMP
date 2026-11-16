module

public import MMP.AlgebraicGeometry.MMP.BasepointFree.Basic
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.SupportingDivisorStein
public import MMP.AlgebraicGeometry.Positivity.Kleiman.AbsoluteCartier
public import MMP.AlgebraicGeometry.Intersection.N1FiniteDimensionalProjective

@[expose] public section

/-!
# Free multiples of a supporting divisor of a negative extremal face

Let `X` be a projective variety over an algebraically closed field `k` of characteristic zero
and `(X, Δ)` a klt pair with `Δ` effective. Let `F` be a `(K_X + Δ)`-negative extremal face of
the closed cone of curves `NE̅(X)`, and `D` a supporting divisor of `F`: a nef Cartier divisor
whose zero set on `NE̅(X)` is exactly `F`. Then `𝒪_X(bD)` is globally generated, that is, the
complete linear system `|bD|` is basepoint free, for every sufficiently large integer `b`.

## Main results

* `MMP.Mori.exists_isGloballyGenerated_sheaf_nsmul_of_isSupportingDivisor`: the statement above.

## Implementation notes

Basepoint freeness of `|bD|` is stated as global generation of the invertible sheaf
`MMP.CartierDivisor.sheaf (b • D)` (`MMP.Intersection.IsGloballyGenerated`):
the evaluation map `H⁰(X, 𝒪_X(bD)) ⊗ 𝒪_X ⟶ 𝒪_X(bD)` is surjective. This is the form in which a
free linear system defines a morphism to projective space. The negativity of `F` is measured by
the form `z ↦ ((K_X + Δ) · z)`, which is `MMP.Fourfold.QDivisor.curveForm` of `K_X + Δ`; this
divisor is `ℚ`-Cartier by the pair condition.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.3 Step 7
-/

section

/-!
## Outline of the proof

Let `(X, Δ)` be a klt pair, `X` projective over an algebraically closed field `k` of
characteristic zero and `Δ` effective, `F` a `(K_X + Δ)`-negative extremal face of `NE̅(X)` and
`D` a supporting divisor of `F`. Then `|bD|` is basepoint free for all `b ≫ 0`.

The face `F` is the zero set of `(D · _)` on `NE̅(X)`, which contains no line, and `K_X + Δ` is
negative on `F \ {0}`; so for some integer `m` the form `m (D · _) - ((K_X + Δ) · _)` is
positive on `NE̅(X) \ {0}`. With `N (K_X + Δ)` Cartier, the Cartier divisor
`N (mW - K_X - Δ)`, `W` the Weil divisor of `D`, is then ample by Kleiman's criterion, hence
`mW - K_X - Δ` is nef and big, and the basepoint-free theorem applies to `W` with `a = m`.

Basepoint freeness of `|bW|` gives global generation of `𝒪_X(bW) ≅ 𝒪_X(bD)`: at a point `x`
outside `Supp (σ)₀` for a section `σ`, any local section `t` is `(t / σ) · σ`, and `t / σ` has
no poles near `x`, so is regular there by algebraic Hartogs.
-/

namespace MMP.FourfoldProofs.Km3bSupportingDivisorFreeMultipleProof

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Intersection

/-! ### The Weil divisor of a Cartier divisor -/

section Weil

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]

/-- On an integral Noetherian scheme every Cartier divisor has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier (A : X.CartierDivisor) :
    ∃ w : Divisor X, IsWeilDivisorOfCartier A w := by
  letI : IsNoetherian X := ⟨⟩
  have h0 : ∀ s ∈ cartierSupport A, Order.coheight s = 0 → False := by
    intro s hs h0
    have : Ring.KrullDimLE 0 (X.presheaf.stalk s) := krullDimLE_of_coheight_le (by simp [h0])
    have : IsArtinianRing (X.presheaf.stalk s) := isArtinianRing_iff_krullDimLE_zero.mpr this
    exact notMem_cartierSupport_of_isArtinianRing A s hs
  have hfin := finite_setOf_genericPoint_mem (isClosed_cartierSupport A) h0
  refine ⟨Finsupp.ofSupportFinite (fun P => primeDivisorOrder P A)
    (hfin.subset fun P hP => ?_), fun P => ?_⟩
  · by_contra h
    have hg : (primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset fun h' => h ?_)
    show P.genericPoint ∈ cartierSupport A
    rw [← hg]
    exact genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact isOrderAlong_primeDivisorOrder A P

omit [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] in
/-- The Weil divisor of `n D` is `n` times the Weil divisor of `D`. -/
private theorem isWeilDivisorOfCartier_nsmul {D : X.CartierDivisor} {w : Divisor X}
    (h : IsWeilDivisorOfCartier D w) (n : ℕ) : IsWeilDivisorOfCartier (n • D) (n • w) := by
  induction n with
  | zero => intro P; simpa using isOrderAlong_zero (primeDivisorSubvariety P)
  | succ n ih =>
    intro P
    rw [succ_nsmul, succ_nsmul, DivisorWithCoeffs.coeff_add]
    exact (ih P).add (h P)

end Weil

/-! ### Global generation -/

section GlobalGeneration

variable {X : Scheme.{0}}

/-- Global generation is invariant under isomorphism of `𝒪_X`-modules. -/
private theorem isGloballyGenerated_of_iso {F G : X.Modules} (e : F ≅ G)
    (hF : IsGloballyGenerated F) : IsGloballyGenerated G := by
  intro x hx U hxU t
  obtain ⟨W, hWU, hxW, m, s, r, h⟩ := hF x hx U hxU (e.inv.app U t)
  refine ⟨W, hWU, hxW, m, fun i => e.hom.app ⊤ (s i), r, ?_⟩
  have h1 := congrArg (e.hom.app W) h
  have hnat : ∀ {V V' : X.Opens} (i : V' ⟶ V) (u : Γ(F, V)),
      e.hom.app V' (F.presheaf.map i.op u) = G.presheaf.map i.op (e.hom.app V u) :=
    fun i u => ConcreteCategory.congr_hom (e.hom.mapPresheaf.naturality i.op) u
  have he : e.hom.app U (e.inv.app U t) = t := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id,
      Scheme.Modules.Hom.id_app]
    rfl
  rw [hnat, he, map_sum] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, hnat]

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- If the linear system `|M|` is basepoint free, the divisorial sheaf `𝒪_X(M)` is globally
generated. -/
private theorem isGloballyGenerated_divisorialSheaf {M : Divisor X} (hM : M.IsBasepointFree) :
    IsGloballyGenerated M.divisorialSheaf := by
  intro x _ U hxU t
  obtain ⟨σ, hσ, hxσ⟩ : ∃ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0),
      x ∉ ((M.zeroDivisor σ hσ).supp : Set X) := by
    by_contra h
    push Not at h
    have hx := (Divisor.mem_baseLocus_iff M x).2 h
    rw [show M.baseLocus = ⊥ from hM] at hx
    exact hx
  set φ := (Divisor.isUnit_sectionToRationalFunctions hσ).unit
  let V : X.Opens := ⟨((M.zeroDivisor σ hσ).supp : Set X)ᶜ,
    (M.zeroDivisor σ hσ).supp.isClosed.isOpen_compl⟩
  let W : X.Opens := U ⊓ V
  have hWU : W ≤ U := inf_le_left
  have hZ : ∀ E : MMP.Mori.PrimeDivisor X, (E.support ∩ (W : Set X)).Nonempty →
      E.ord φ + M.coeff E = 0 := by
    rintro E ⟨y, hyE, hyW⟩
    by_contra hne
    have : (M.zeroDivisor σ hσ).coeff E ≠ 0 := by
      rwa [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
    exact hyW.2 (DivisorWithCoeffs.support_subset_supp this hyE)
  let t' : M.divisorialSubmodule W := M.divisorialRestrict (homOfLE hWU) t
  have hcoef : ∀ E : MMP.Mori.PrimeDivisor X,
      M.coeff E = (M + principalDivisor φ).coeff E + E.ord φ⁻¹ := fun E => by
    simp [DivisorWithCoeffs.coeff_add, coeff_principalDivisor, PrimeDivisor.ord_inv]
  have hr : (0 : Divisor X).IsDivisorialSection W
      (Divisor.divisorialMulLinearMap φ⁻¹ hcoef W t').1 := by
    intro E hE
    have := (Divisor.divisorialMulLinearMap φ⁻¹ hcoef W t').2 E hE
    rwa [DivisorWithCoeffs.coeff_add, coeff_principalDivisor, add_comm, hZ E hE] at this
  obtain ⟨s, hs⟩ := Divisor.IsDivisorialSection.exists_eq hr
  refine ⟨W, hWU, ⟨hxU, hxσ⟩, 1, fun _ => σ, fun _ => s, ?_⟩
  rw [Fin.sum_univ_one]
  apply Subtype.ext
  funext Z
  have hsZ : X.presheaf.germ W _ Z.2 s =
      ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 * t.1 ⟨Z.1, hWU Z.2⟩ :=
    congrFun hs Z
  have hinv : ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 *
      σ.1 ⟨Z.1, trivial⟩ = 1 := by
    change ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1 *
      (φ : RationalFunctions X) Z.1 = 1
    rw [← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Pi.one_apply]
  change t.1 ⟨Z.1, hWU Z.2⟩ = X.presheaf.germ W _ Z.2 s * σ.1 ⟨Z.1, trivial⟩
  rw [hsZ, mul_comm, ← mul_assoc, mul_comm (σ.1 _), hinv, one_mul]

end GlobalGeneration

/-! ### Curves and degrees -/

section Curves

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- A closed immersion with reduced source has kernel the vanishing ideal of its image. -/
private theorem ker_eq_vanishingIdeal_support {A B : Scheme.{0}} (g : A ⟶ B)
    [IsClosedImmersion g] [IsReduced A] :
    g.ker = Scheme.IdealSheafData.vanishingIdeal g.ker.support := by
  have hg : IsIso g.toImage := by
    apply IsClosedImmersion.isIso_of_ker_eq g g.imageι g.toImage <;> simp [Scheme.Hom.imageι]
  have : IsReduced g.ker.subscheme := isReduced_of_isOpenImmersion (asIso g.toImage).inv
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme g.ker g.ker.support rfl

/-- On a proper `k`-scheme, for an integral one-dimensional closed subscheme `i : C ⟶ X` there is a
proper curve `Γ` on which every invertible sheaf has the same degree as on `i`. -/
private theorem exists_properCurve_degreeOn_eq [IsProper sX] {C : Scheme.{0}} (i : C ⟶ X)
    [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)] (hC : topologicalKrullDim C = 1) :
    ∃ Γ : ProperCurve sX, ∀ (L : X.Modules)
      [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      degreeOn k sX i hC.le L = Γ.degree k L := by
  set x : X := i (genericPoint C) with hx
  have hrange : Set.range i = closure ({x} : Set X) := by
    rw [← Set.image_univ, ← (genericPoint_spec C).def, ← i.isClosedEmbedding.closure_image_eq,
      Set.image_singleton]
  have hsupp : i.ker.support = TopologicalSpace.Closeds.closure ({x} : Set X) := by
    apply TopologicalSpace.Closeds.ext
    rw [Scheme.Hom.support_ker, TopologicalSpace.Closeds.coe_closure, hrange, closure_closure]
  have hker : i.ker = (curveSubschemeAtι x).ker := by
    rw [ker_eq_vanishingIdeal_support i, hsupp, Scheme.IdealSheafData.ker_subschemeι]
  haveI := IsClosedImmersion.isIso_lift (curveSubschemeAtι x) i hker.symm
  let e : C ≅ curveSubschemeAt x :=
    asIso (IsClosedImmersion.lift (curveSubschemeAtι x) i hker.symm.le)
  have hdimx : topologicalKrullDim (curveSubschemeAt x) = 1 := by
    rw [← hC]
    exact (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).symm
  exact ⟨⟨x, isProperCurve_of_isProper sX hdimx⟩, fun L _ =>
    MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX i _ hC.le hdimx.le e
      (IsClosedImmersion.lift_fac _ _ _) L⟩

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]

/-- The degree of the Weil divisor `w` of a Cartier divisor `D` along a curve is that of
`𝒪_X(D)`. -/
private theorem degreeOn_eq_of_isWeilDivisorOfCartier {D : X.CartierDivisor} {w : Divisor X}
    (h : IsWeilDivisorOfCartier D w) {C : Scheme.{0}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hC : topologicalKrullDim C ≤ 1) :
    w.degreeOn k sX i hC h.isCartier =
      degreeOn k sX i hC (MMP.CartierDivisor.sheaf D) := by
  haveI := h.isCartier.isInvertibleModule_divisorialSheaf
  exact (degreeOn_eq_of_iso k sX i hC h.sheafIsoDivisorialSheaf).symm

/-- The Weil divisor of a nef Cartier divisor on a proper `k`-scheme is nef. -/
private theorem isNef_of_isWeilDivisorOfCartier [IsProper sX] {D : X.CartierDivisor}
    {w : Divisor X} (h : IsWeilDivisorOfCartier D w)
    (hD : (KCartierDivisor.ofCartier ℝ D).IsNef k sX) : w.IsNef k sX := by
  refine ⟨h.isCartier, fun C i _ _ _ hC => ?_⟩
  obtain ⟨Γ, hΓ⟩ := exists_properCurve_degreeOn_eq sX i hC
  rw [degreeOn_eq_of_isWeilDivisorOfCartier sX h i hC.le, hΓ]
  have := hD Γ
  rw [MMP.ProgramBaseChange.intersectionNumber_cycle_ofCartier] at this
  exact_mod_cast this

end Curves

/-! ### The numerical topology -/

section Topology

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- Addition and negation are continuous for the numerical topology. -/
private theorem isTopologicalAddGroup_numericalCurveClasses :
    IsTopologicalAddGroup (NumericalCurveClasses sX) :=
  topologicalAddGroup_iInf fun L => topologicalAddGroup_iInf fun h =>
    haveI := h; topologicalAddGroup_induced (NumericalCurveClasses.degree sX L)

/-- Scalar multiplication is jointly continuous for the numerical topology. -/
private theorem continuousSMul_numericalCurveClasses :
    ContinuousSMul ℝ (NumericalCurveClasses sX) :=
  continuousSMul_iInf fun L => continuousSMul_iInf fun h =>
    haveI := h; continuousSMul_induced (NumericalCurveClasses.degree sX L)

/-- The numerical topology is Hausdorff: the degree forms separate numerical classes. -/
private theorem t2Space_numericalCurveClasses : T2Space (NumericalCurveClasses sX) := by
  refine T2Space.of_injective_continuous (f := fun z (p : Σ' L : X.Modules,
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) =>
      haveI := p.2; NumericalCurveClasses.degree sX p.1 z) ?_
    (continuous_pi fun p => haveI := p.2; NumericalCurveClasses.continuous_degree sX p.1)
  intro z z' hzz'
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  obtain ⟨Z', rfl⟩ := OneCycle.numericalClass_surjective sX z'
  refine OneCycle.numericalClass_eq_iff.mpr fun L hL => ?_
  exact congrFun hzz' ⟨L, hL⟩

end Topology

/-- The closed cone of curves of a projective variety is salient. -/
private theorem closedConeOfCurves_inter_neg_eq_zero {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [AlgebraicGeometry.IsProjectiveVariety k sX] :
    (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) ∩
      -(closedConeOfCurves sX : Set (NumericalCurveClasses sX)) = {0} := by
  ext z
  refine ⟨fun ⟨h1, h2⟩ => ?_, ?_⟩
  · have : z ∈ (closedConeOfCurves sX).lineal := PointedCone.mem_lineal.2 ⟨h1, h2⟩
    rwa [lineal_closedConeOfCurves_eq_bot sX] at this
  · rintro rfl
    exact ⟨zero_mem _, by simp⟩

/-- A nef Cartier divisor is nonnegative on the closed cone of curves. -/
private theorem intersectionNumber_nonneg_of_isNef {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [AlgebraicGeometry.IsProjectiveVariety k sX]
    {D : X.CartierDivisor} (hD : (KCartierDivisor.ofCartier ℝ D).IsNef k sX) :
    ∀ z ∈ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)),
      0 ≤ NumericalCurveClasses.intersectionNumber (sX := sX)
        (KCartierDivisor.ofCartier ℝ D) z := by
  intro z hz
  have := (KCartierDivisor.isNef_iff_closedConeOfCurves_subset_nonnegHalfspace (k := k)
    (sX := sX) _).1 hD hz
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  exact this Z rfl

/-- If `m D - (K + Δ)` is positive on `NE̅(X) \ {0}`, then `m W - K - Δ` is ample, where `W` is
the Weil divisor of `D`. -/
private theorem isAmple_smul_sub_of_pos {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [AlgebraicGeometry.IsProjectiveVariety k sX]
    {K : Divisor X} {Δ : QDivisor X} (hq : (Divisor.toQDivisor K + Δ).IsQCartier)
    {D : X.CartierDivisor} {W : Divisor X} (hW : IsWeilDivisorOfCartier D W) {m : ℕ}
    (hpos : ∀ z ∈ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)), z ≠ 0 →
      0 < (m : ℝ) * NumericalCurveClasses.intersectionNumber (sX := sX)
        (KCartierDivisor.ofCartier ℝ D) z -
        MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hq z) :
    ((m : ℚ) • Divisor.toQDivisor W - Divisor.toQDivisor K - Δ).IsAmple := by
  haveI : IsProper sX := inferInstance
  have hWc : W.IsCartier := hW.isCartier
  obtain ⟨N, hN, EK, hEK, hEKc⟩ := hq.exists_pos
  set φ := MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hq with hφdef
  set l := NumericalCurveClasses.intersectionNumber (sX := sX)
    (KCartierDivisor.ofCartier ℝ D) with hldef
  have hlC : ∀ C : ProperCurve sX, l (OneCycle.numericalClass sX (C.cycle ℝ)) =
      (W.degreeOn k sX C.ι C.dim_le hWc : ℝ) := by
    intro C
    rw [hldef, NumericalCurveClasses.intersectionNumber_numericalClass,
      MMP.ProgramBaseChange.intersectionNumber_cycle_ofCartier, ProperCurve.degree,
      degreeOn_eq_of_isWeilDivisorOfCartier sX hW]
  have hφC : ∀ C : ProperCurve sX, φ (OneCycle.numericalClass sX (C.cycle ℝ)) =
      (EK.degreeOn k sX C.ι C.dim_le hEKc : ℝ) / N := by
    intro C
    rw [hφdef, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
      QDivisor.intersectionNumber_eq_of_smul k sX C.ι C.dim_le _ hq hN EK hEKc hEK]
    push_cast
    rfl
  set AW : Divisor X := (N * m) • W - EK with hAWdef
  have hAWc : AW.IsCartier := (hWc.nsmul _).sub hEKc
  haveI := hAWc.isInvertibleModule_divisorialSheaf
  obtain ⟨A, ⟨eA⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf AW.divisorialSheaf
  have hAform : NumericalCurveClasses.intersectionNumber (sX := sX)
      (KCartierDivisor.ofCartier ℝ A) = (N : ℝ) • ((m : ℝ) • l - φ) := by
    apply MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle
    intro C
    rw [NumericalCurveClasses.intersectionNumber_numericalClass,
      MMP.ProgramBaseChange.intersectionNumber_cycle_ofCartier, ProperCurve.degree,
      ← degreeOn_eq_of_iso k sX C.ι C.dim_le eA]
    change ((AW.degreeOn k sX C.ι C.dim_le hAWc : ℤ) : ℝ) = _
    rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply, hlC, hφC,
      Divisor.degreeOn_congr (sub_eq_add_neg _ _) hAWc ((hWc.nsmul _).add hEKc.neg),
      Divisor.degreeOn_add k sX C.ι C.dim_le _ _ (hWc.nsmul _) hEKc.neg,
      Divisor.degreeOn_nsmul' k sX C.ι C.dim_le W hWc,
      Divisor.degreeOn_neg' k sX C.ι C.dim_le EK hEKc]
    have hinv : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast hN.ne')
    push_cast
    linear_combination (EK.degreeOn k sX C.ι C.dim_le hEKc : ℝ) * hinv
  have hAamp : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf A) :=
    (isAmple_cartierSheaf_iff_forall_closedConeOfCurves_pos sX A).2 fun z hz hz0 => by
      rw [hAform, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        smul_eq_mul]
      exact mul_pos (by exact_mod_cast hN) (hpos z hz hz0)
  have hAWamp : AW.IsAmple hAWc := (Stacks.RelativeVeryAmple.isAmple_congr _ _ eA).2 hAamp
  refine ⟨N, hN, AW, ?_, hAWc, hAWamp⟩
  rw [hAWdef, map_sub, map_nsmul, hEK, ← Nat.cast_smul_eq_nsmul ℚ,
    ← Int.cast_smul_eq_zsmul ℚ]
  push_cast
  module

end MMP.FourfoldProofs.Km3bSupportingDivisorFreeMultipleProof

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open MMP.FourfoldProofs.Km3bSupportingDivisorFreeMultipleProof in
/-- **Free multiples of a supporting divisor** (Kollár–Mori 3.3, Step 7). Let `X` be a projective
variety over an algebraically closed field `k` of characteristic zero, `(X, Δ)` a klt pair with
canonical divisor `K` and `Δ` effective, `F` a `(K + Δ)`-negative extremal face of `NE̅(X)`, and
`D` a supporting divisor of `F`. Then there is `b₀` such that `𝒪_X(bD)` is globally generated
(`|bD|` is basepoint free) for every `b ≥ b₀`. -/
@[mmp "lem_km3b_supporting_divisor_free_multiple"]
public theorem exists_isGloballyGenerated_sheaf_nsmul_of_isSupportingDivisor {k : Type}
    [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective)
    {F : Set (NumericalCurveClasses sX)}
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F)
    {D : X.CartierDivisor} (hD : IsSupportingDivisor k sX F D) :
    ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
      MMP.Intersection.IsGloballyGenerated (MMP.CartierDivisor.sheaf (b • D)) := by
  haveI : IsProper sX := inferInstance
  obtain ⟨W, hW⟩ := exists_isWeilDivisorOfCartier D
  have hWc : W.IsCartier := hW.isCartier
  haveI := isTopologicalAddGroup_numericalCurveClasses sX
  haveI := continuousSMul_numericalCurveClasses sX
  haveI := t2Space_numericalCurveClasses sX
  haveI := NumericalCurveClasses.finiteDimensional_of_isProjectiveVariety sX
  obtain ⟨m₀, hm₀⟩ := MMP.Positivity.exists_forall_ge_pos_smul_sub
    (isCone_coe (closedConeOfCurves sX)) (closedConeOfCurves sX).convex
    (by rw [coe_closedConeOfCurves]; exact isClosed_closure)
    (closedConeOfCurves_inter_neg_eq_zero sX)
    (intersectionNumber_nonneg_of_isNef sX hD.1) hD.2 hF.2.2
  obtain ⟨m, hm⟩ := exists_nat_ge (max m₀ 1)
  have hm1 : (1 : ℝ) ≤ m := le_trans (le_max_right _ _) hm
  have hpos := hm₀ m (le_trans (le_max_left _ _) hm)
  have hBamp := isAmple_smul_sub_of_pos sX hklt.1.2.2 hW hpos
  obtain ⟨hBnef, hBbig⟩ := QDivisor.isNef_and_isBig_of_isAmple sX hBamp
  have hdat : IsBasepointFreeDatum sX n K Δ W (m : ℚ) :=
    { isProperVariety := inferInstance
      isKltPair := hklt
      isEffective := hΔ
      isCartier := hWc
      isNef := isNef_of_isWeilDivisorOfCartier sX hW hD.1
      pos := by exact_mod_cast (show (0 : ℝ) < m by linarith)
      isQCartier_sub := hBnef.1
      isNef_sub := hBnef
      isBig_sub := hBbig }
  obtain ⟨b₀, hb₀⟩ := hdat.exists_isBasepointFree_nsmul
  exact ⟨b₀, fun b hb => isGloballyGenerated_of_iso
    (isWeilDivisorOfCartier_nsmul hW b).sheafIsoDivisorialSheaf.symm
    (isGloballyGenerated_divisorialSheaf (hb₀ b hb))⟩

end MMP.Mori

end
