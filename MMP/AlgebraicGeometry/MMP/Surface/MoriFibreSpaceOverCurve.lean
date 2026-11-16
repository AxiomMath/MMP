module

public import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
public import MMP.AlgebraicGeometry.Intersection.SelfIntersectionHilbertDegree
public import MMP.AlgebraicGeometry.Intersection.Surface.BlowupGenusDropAdjunction
public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.GenericFibreDegree
public import MMP.AlgebraicGeometry.MMP.Abundance.NormalizedSectionDegreeZero
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.ProjectiveLineProperties
public import MMP.AlgebraicGeometry.MMP.Contraction.NumericallyTrivialDescent
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal

section

/-!
# Rank-one surface fibrations and the two-branch residue identification

Let `g : V ⟶ T` be a Mori fibre space of a `ℚ`-factorial projective surface onto a normal
projective curve, for a klt lowering `B - ε⌊B⌋` of an lc boundary `B` with `K_V + B ≡_T 0`.

* Every closed fibre is irreducible. The intersection forms of contracted curves are
  proportional because `ρ(V/T) = 1`. So a component `E₁` of a reducible fibre is nonnegative on
  every contracted curve, and Zariski's lemma along the fibre, applied to `g^*t - E₁`, gives a
  contradiction.
* The horizontal floor is a section, a bisection or two sections. At a general closed fibre `C`,
  the generic fibre degree of a divisor is its intersection number with `C`. Adjunction on the
  smooth locus gives `K · C ≥ -2`, hence `B · C ≤ 2`, while `⌊B⌋ · C > 0`.
* A section of generic degree one is a finite birational map onto the normal curve `T`, hence an
  isomorphism, and so is any finite birational `N ⟶ P`.
* `g` is the contraction of a `(K + B - ε⌊B⌋)`-negative extremal ray, so relatively trivial
  divisors descend to `T`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

open CategoryTheory AlgebraicGeometry MMP MMP.Mori MMP.Fourfold

@[expose] public section

namespace MMP.FourfoldProofs.MmpSurfaceRankOneFloorResidueLinkProof

/-- In a real vector space of rank one, two linear forms are proportional. -/
private theorem mul_comm_of_toENat_rank_eq_one {Q : Type*} [AddCommGroup Q] [Module ℝ Q]
    (hQ : (Module.rank ℝ Q).toENat = 1) (φ ψ : Q →ₗ[ℝ] ℝ) (a b : Q) :
    φ a * ψ b = φ b * ψ a := by
  have h1 : Module.rank ℝ Q = 1 := by
    rwa [Cardinal.toENat_eq_one] at hQ
  have : Module.finrank ℝ Q = 1 := Module.finrank_eq_of_rank_eq (by simpa using h1)
  obtain ⟨e, -, he⟩ := finrank_eq_one_iff'.mp this
  obtain ⟨α, rfl⟩ := he a
  obtain ⟨β, rfl⟩ := he b
  simp only [map_smul, smul_eq_mul]; ring

/-- The intersection form of a curve contracted by `f` vanishes on `f^* N¹(Z)_ℝ`. -/
private theorem pullbackNumericalClasses_le_ker {k : Type} [Field k] {X Z : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [IsSeparated sZ] [LocallyOfFiniteType sZ]
    (f : X ⟶ Z) (hf : f ≫ sZ = sX) (γ : ProperCurve sX) (hγ : γ.IsContractedBy f) :
    pullbackNumericalClasses sX f ≤
      LinearMap.ker ((numericalPairing sX).flip (OneCycle.numericalClass sX (γ.cycle ℝ))) := by
  rw [pullbackNumericalClasses, Submodule.span_le]
  rintro d ⟨E, M, hM, ⟨e⟩, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply, numericalPairing_apply]
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
  have h0 := γ.degree_pullback_eq_zero_of_isContractedBy f hf hγ M
  have h1 : γ.degree k (MMP.CartierDivisor.sheaf E) =
      γ.degree k ((Scheme.Modules.pullback f).obj M) :=
    degreeOn_eq_of_iso k sX γ.ι γ.dim_le e
  rw [h1, h0, Int.cast_zero]

/-- **Proportionality of contracted curves.** If `ρ(X/Z) = 1`, the intersection forms of any two
curves contracted by `f` are proportional on `N¹(X)_ℝ`. -/
private theorem curveForm_mul_comm {k : Type} [Field k] {X Z : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [IsSeparated sZ] [LocallyOfFiniteType sZ]
    (f : X ⟶ Z) (hf : f ≫ sZ = sX) (hρ : relativePicardNumberN1 sX f = 1)
    (γ γ' : ProperCurve sX) (hγ : γ.IsContractedBy f) (hγ' : γ'.IsContractedBy f)
    (a b : NumericalDivisorClasses sX) :
    numericalPairing sX a (OneCycle.numericalClass sX (γ.cycle ℝ)) *
        numericalPairing sX b (OneCycle.numericalClass sX (γ'.cycle ℝ)) =
      numericalPairing sX b (OneCycle.numericalClass sX (γ.cycle ℝ)) *
        numericalPairing sX a (OneCycle.numericalClass sX (γ'.cycle ℝ)) := by
  set W := pullbackNumericalClasses sX f
  have h := mul_comm_of_toENat_rank_eq_one hρ
    (W.liftQ _ (pullbackNumericalClasses_le_ker sX sZ f hf γ hγ))
    (W.liftQ _ (pullbackNumericalClasses_le_ker sX sZ f hf γ' hγ')) (W.mkQ a) (W.mkQ b)
  simpa using h

/-- The intersection form of a curve on the class of a Cartier divisor is its degree. -/
private theorem exists_numericalPairing_eq_degreeOn {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [QuasiCompact sX] (D : Divisor X) (hD : D.IsCartier) :
    ∃ d : NumericalDivisorClasses sX, ∀ γ : ProperCurve sX,
      numericalPairing sX d (OneCycle.numericalClass sX (γ.cycle ℝ)) =
        (D.degreeOn k sX γ.ι γ.dim_le hD : ℝ) := by
  have := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨E, ⟨e⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  refine ⟨numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ E), fun γ => ?_⟩
  rw [numericalPairing_apply, OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree,
    OneCycle.degree_cycle]
  have h1 : γ.degree k (MMP.CartierDivisor.sheaf E) =
      Mori.degreeOn k sX γ.ι γ.dim_le D.divisorialSheaf :=
    (degreeOn_eq_of_iso k sX γ.ι γ.dim_le e).symm
  rw [h1]
  rfl

/-- The generic point of a prime divisor of a proper surface is the generic point of a proper
curve. -/
private theorem isProperCurve_genericPoint_of_dim_eq_two {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsProper sX] [IsIntegral X] [LocallyOfFiniteType sX]
    (hdim : topologicalKrullDim X = 2) (P : Mori.PrimeDivisor X) :
    IsProperCurve sX P.genericPoint := by
  refine isProperCurve_of_isProper sX ?_
  have h1 := MMP.Intersection.subvarietyDim_eq_height
    (MMP.Intersection.associatedSubvariety P.genericPoint)
  rw [MMP.Intersection.genericPoint_associatedSubvariety] at h1
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := ‹LocallyOfFiniteType sX›
  have hpure : MMP.Intersection.IsPureDimensional X 2 := by
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [(Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq, hdim]
    rfl
  have h2 := MMP.Intersection.height_add_coheight_eq_of_isPureDimensional k hpure P.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P] at h2
  have h3 : Order.height P.genericPoint = 1 :=
    WithTop.add_right_cancel ENat.one_ne_top (h2.trans one_add_one_eq_two.symm)
  change topologicalKrullDim (curveSubschemeAt P.genericPoint) = 1
  exact h1.trans (by rw [h3]; rfl)

/-- **The fibre divisor.** A closed point `t` of a normal curve `T` is a Cartier prime divisor,
and its pull-back `F = g^*t` along a dominant map from a normal integral scheme exists. -/
private theorem exists_isPullback_fibre {V T : Scheme.{0}}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [CompactSpace V] (g : V ⟶ T) (hsurj : Function.Surjective g.base)
    (hdimT : topologicalKrullDim T = 1) (t : T) (ht : IsClosed ({t} : Set T)) :
    ∃ (P : Mori.PrimeDivisor T) (_ : P.genericPoint = t)
      (hB : ∀ Z : irreducibleComponents V,
        g (componentGenericPoint V Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor T))
      (F : Divisor V), Divisor.IsPullback g (Finsupp.single P 1 : Divisor T) hB F := by
  classical
  have hgenX : ∀ Z : irreducibleComponents V, g (componentGenericPoint V Z) = genericPoint T := by
    intro Z
    have hZ : Z.1 = Set.univ := by
      have h : Z.1 ∈ ({Set.univ} : Set (Set V)) :=
        (irreducibleComponents_eq_singleton (X := V)) ▸ Z.2
      exact h
    have hgp := isGenericPoint_componentGenericPoint V Z
    rw [hZ] at hgp
    refine IsGenericPoint.eq ?_ (genericPoint_spec T)
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨x, rfl⟩ := hsurj y
    have hx : x ∈ closure {componentGenericPoint V Z} := by rw [hgp.def]; trivial
    have := image_closure_subset_closure_image g.continuous ⟨x, hx, rfl⟩
    rwa [Set.image_singleton] at this
  have hη : ∀ (D : Divisor T) (Z : irreducibleComponents V),
      g (componentGenericPoint V Z) ∉ D.supp := fun D Z => by
    rw [hgenX]; exact genericPoint_notMem_supp D
  have htne : t ≠ genericPoint T := fun h => not_isClosed_genericPoint hdimT (h ▸ ht)
  set P : Mori.PrimeDivisor T := AlgebraicGeometry.PrimeDivisor.ofCoheightOne t
    (coheight_eq_one_of_ne_genericPoint hdimT htne)
  have hPt : P.genericPoint = t := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hPc : IsClosed ({P.genericPoint} : Set T) := hPt ▸ ht
  have hcart : Divisor.IsCartier (Finsupp.single P 1 : Divisor T) := by
    intro x
    by_cases hx : x = t
    · obtain ⟨U, ϖ, φ, hxU, -, -, hφ⟩ :=
        exists_isLocalEquation_single_of_eq P x (hPt.trans hx.symm)
      exact ⟨U, hxU, φ, hφ⟩
    · refine ⟨⟨{t}ᶜ, ht.isOpen_compl⟩, hx, 1, ?_⟩
      rintro E' ⟨x', hxE', hxU⟩
      have hE'P : E' ≠ P := by
        rintro rfl
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hPc.closure_eq, hPt] at hxE'
        exact hxU hxE'
      rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hE'P), PrimeDivisor.ord_one]
  exact ⟨P, hPt, hη _, _, Divisor.isPullback_pullback hcart (hη _)⟩

/-- **Fibres of a rank-one fibration over a curve are irreducible.** -/
private theorem isIrreducible_fibre {k : Type} [Field k] {V T : Scheme.{0}}
    (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [IsSeparated sT] [LocallyOfFiniteType sT] [IsProper sV] [LocallyOfFiniteType sV]
    (g : V ⟶ T) [IsProper g]
    (hdimV : topologicalKrullDim V = 2) (hQ : IsQFactorial sV)
    (hgs : g ≫ sT = sV) (hO : ∀ U : T.Opens, IsIso (g.app U))
    (hsurj : Function.Surjective g.base)
    (hρ : relativePicardNumberN1 sV g = 1) (hdimT : topologicalKrullDim T = 1)
    (L : Divisor V) (hL : L.IsCartier)
    (hpos : ∀ γ : ProperCurve sV, γ.IsContractedBy g → 0 < L.degreeOn k sV γ.ι γ.dim_le hL)
    (t : T) (ht : IsClosed ({t} : Set T)) : IsIrreducible (g.base ⁻¹' {t}) := by
  classical
  obtain ⟨P, hPt, hB, F, hF⟩ := exists_isPullback_fibre g hsurj hdimT t ht
  have hPc : IsClosed ({P.genericPoint} : Set T) := hPt ▸ ht
  have hover : ∀ E, F E ≠ 0 → g E.genericPoint = t := fun E hE => by
    by_contra h
    exact hE (coeff_eq_zero_of_isPullback_single g P hPc hF E (hPt ▸ h))
  have hpos' : ∀ E : Mori.PrimeDivisor V, g E.genericPoint = t → 0 < F E := fun E hE =>
    coeff_pos_of_isPullback_single g P hF E (hE.trans hPt.symm)
  have hsupp_sub : ∀ E : Mori.PrimeDivisor V, g E.genericPoint = t →
      E.support ⊆ g.base ⁻¹' {t} := by
    intro E hE x hx
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
    have h1 := (specializes_iff_mem_closure.mpr hx).map g.continuous
    rw [hE] at h1
    have := specializes_iff_mem_closure.mp h1
    rwa [ht.closure_eq] at this
  have hfib_sub : g.base ⁻¹' {t} ⊆ ⋃ E ∈ F.support, E.support := by
    intro x hx
    have hxF := mem_supp_of_isPullback_single g P hF (x := x) (hPt ▸ hx)
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxF
    exact Set.mem_iUnion₂.mpr ⟨E, Finsupp.mem_support_iff.mpr hE, hxE⟩
  by_contra hirr
  obtain ⟨E₁, h₁, E₂, h₂, hne⟩ : ∃ E₁ ∈ F.support, ∃ E₂ ∈ F.support, E₁ ≠ E₂ := by
    by_contra h
    push Not at h
    obtain ⟨x, hx⟩ := hsurj t
    obtain ⟨E, hE, -⟩ := Set.mem_iUnion₂.mp (hfib_sub (show x ∈ g.base ⁻¹' {t} from hx))
    have heq : g.base ⁻¹' {t} = E.support := by
      refine subset_antisymm (fun y hy => ?_)
        (hsupp_sub E (hover E (Finsupp.mem_support_iff.mp hE)))
      obtain ⟨E', hE', hyE'⟩ := Set.mem_iUnion₂.mp (hfib_sub hy)
      rwa [h E' hE' E hE] at hyE'
    apply hirr
    rw [heq, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  have ht₁ := hover E₁ (Finsupp.mem_support_iff.mp h₁)
  have ht₂ := hover E₂ (Finsupp.mem_support_iff.mp h₂)
  -- the contracted curves
  have hcontr : ∀ E : Mori.PrimeDivisor V, g E.genericPoint = t →
      (⟨E.genericPoint, isProperCurve_genericPoint_of_dim_eq_two sV hdimV E⟩ :
        ProperCurve sV).IsContractedBy g := by
    intro E hE x hx
    exact (hsupp_sub E hE (by rwa [AlgebraicGeometry.PrimeDivisor.support_eq_closure])).trans
      hE.symm
  set γ₂ : ProperCurve sV := ⟨E₂.genericPoint, isProperCurve_genericPoint_of_dim_eq_two sV hdimV E₂⟩
  have hγ₂ : γ₂.IsContractedBy g := hcontr E₂ ht₂
  set D₁ : QDivisor V := Divisor.toQDivisor (Finsupp.single E₁ 1)
  have hD₁ : D₁.IsQCartier := isQCartier_of_isQFactorial sV hQ D₁
  have hD₁0 : 0 ≤ D₁ := fun E => by
    change (0 : ℚ) ≤ DivisorWithCoeffs.coeff (Divisor.toQDivisor (Finsupp.single E₁ 1)) E
    rw [Divisor.coeff_toQDivisor]
    by_cases h : E = E₁
    · subst h; rw [DivisorWithCoeffs.coeff_single_self]; simp
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm h)]; simp
  have hnotin : γ₂.point ∉ D₁.supp := by
    intro hmem
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    have hE1 : E = E₁ := by
      by_contra h
      apply hE
      change DivisorWithCoeffs.coeff (Divisor.toQDivisor (Finsupp.single E₁ 1)) E = 0
      rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_single_of_ne (Ne.symm h)]; simp
    subst hE1
    exact hne (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E E₂ hxE)
  have h12 := (intersectionNumber_nonneg_and_eq_zero_iff sV D₁ hD₁ hD₁0 γ₂ hnotin).1
  -- `D₁` is nonnegative on every contracted curve
  obtain ⟨m, hm, E, hEq, hEc⟩ := hD₁.exists_pos
  obtain ⟨d₁, hd₁⟩ := exists_numericalPairing_eq_degreeOn sV E hEc
  obtain ⟨dL, hdL⟩ := exists_numericalPairing_eq_degreeOn sV L hL
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  have hD₁nn : ∀ γ : ProperCurve sV, γ.IsContractedBy g →
      0 ≤ D₁.intersectionNumber k sV γ.ι γ.dim_le hD₁ := by
    intro γ hγ
    have key := curveForm_mul_comm sV sT g hgs hρ γ γ₂ hγ hγ₂ d₁ dL
    rw [hd₁, hd₁, hdL, hdL] at key
    have hp1 : (0 : ℝ) < L.degreeOn k sV γ.ι γ.dim_le hL := by exact_mod_cast hpos γ hγ
    have hp2 : (0 : ℝ) < L.degreeOn k sV γ₂.ι γ₂.dim_le hL := by exact_mod_cast hpos γ₂ hγ₂
    have h2 : (0 : ℝ) ≤ E.degreeOn k sV γ₂.ι γ₂.dim_le hEc := by
      have := QDivisor.intersectionNumber_eq_of_smul k sV γ₂.ι γ₂.dim_le D₁ hD₁ hm E hEc hEq
      rw [this] at h12
      have : (0 : ℚ) ≤ E.degreeOn k sV γ₂.ι γ₂.dim_le hEc := by
        have := mul_nonneg h12 hmq.le
        rwa [div_mul_cancel₀ _ hmq.ne'] at this
      exact_mod_cast this
    have h3 : (0 : ℝ) ≤ E.degreeOn k sV γ.ι γ.dim_le hEc := by
      have h4 : 0 ≤ (L.degreeOn k sV γ.ι γ.dim_le hL : ℝ) *
          (E.degreeOn k sV γ₂.ι γ₂.dim_le hEc : ℝ) := mul_nonneg hp1.le h2
      rw [← key] at h4
      exact nonneg_of_mul_nonneg_left h4 hp2
    rw [QDivisor.intersectionNumber_eq_of_smul k sV γ.ι γ.dim_le D₁ hD₁ hm E hEc hEq]
    have : (0 : ℚ) ≤ E.degreeOn k sV γ.ι γ.dim_le hEc := by exact_mod_cast h3
    exact div_nonneg this hmq.le
  -- the fibre divisor is numerically trivial on contracted curves
  have hFq : (Divisor.toQDivisor F).IsQCartier := isQCartier_of_isQFactorial sV hQ _
  have hF0 : ∀ γ : ProperCurve sV, γ.IsContractedBy g →
      (Divisor.toQDivisor F).intersectionNumber k sV γ.ι γ.dim_le hFq = 0 := by
    intro γ hγ
    by_cases hγt : g γ.point = t
    · refine intersectionNumber_eq_zero_of_isPullback_single g sV hQ P hF hFq γ fun x hx => ?_
      rw [hγ x (specializes_iff_mem_closure.mp hx), hγt, hPt]
    · refine intersectionNumber_eq_zero_of_disjoint sV hQ _ hFq γ fun x hx hxF => ?_
      rw [Divisor.supp_toQDivisor] at hxF
      obtain ⟨E', hE', hxE'⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxF
      exact hγt ((hγ x (specializes_iff_mem_closure.mp hx)).symm.trans
        (hsupp_sub E' (hover E' hE') hxE'))
  -- Zariski's lemma for `A = F - E₁`
  set A : QDivisor V := Divisor.toQDivisor F - D₁
  have hAE : ∀ E, A E = (F E : ℚ) - (if E = E₁ then 1 else 0) := fun E => by
    by_cases h : E = E₁
    · subst h; simp [A, D₁, Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffs]
    · simp [A, D₁, Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffs, h]
  have hF0' : ∀ E, 0 ≤ F E := fun E => by
    by_cases h : g E.genericPoint = t
    · exact (hpos' E h).le
    · by_contra hlt
      exact h (hover E (by omega))
  have hA0 : 0 ≤ A := fun E => by
    change (0 : ℚ) ≤ A E
    rw [hAE]
    by_cases h : E = E₁
    · subst h
      have := hpos' E ht₁
      simp only [if_true]
      have : (1 : ℚ) ≤ F E := by exact_mod_cast this
      linarith
    · simp only [h, if_false, sub_zero]
      exact_mod_cast hF0' E
  have hnA : (-A).IsQCartier := isQCartier_of_isQFactorial sV hQ _
  have hnef : (-A).IsRelativelyNef sV g := by
    refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sV hnA fun γ hγ => ?_
    have hsum : -A + Divisor.toQDivisor F = D₁ := by
      simp only [A]; abel
    have hcongr : ∀ (D D' : QDivisor V) (hD : D.IsQCartier) (hD' : D'.IsQCartier), D = D' →
        D.intersectionNumber k sV γ.ι γ.dim_le hD =
          D'.intersectionNumber k sV γ.ι γ.dim_le hD' := by
      rintro D _ hD hD' rfl; rfl
    have h1 := QDivisor.intersectionNumber_add' k sV γ.ι γ.dim_le (-A) (Divisor.toQDivisor F)
      hnA hFq (hsum ▸ hD₁)
    rw [hcongr _ _ (hsum ▸ hD₁) hD₁ hsum, hF0 γ hγ, add_zero] at h1
    rw [← h1]
    exact hD₁nn γ hγ
  have hfib : ∀ y : T, _root_.IsPreconnected (g.base ⁻¹' {y}) := fun y =>
    (g.isConnected_preimage_singleton_of_isIso_app hO y).isPreconnected
  obtain ⟨s, -, hs⟩ := exists_coeff_eq_mul_of_isPullback_single sV g hQ hfib P hPc hF A hA0 hnef
  have hs₂ := hs E₂ (ht₂.trans hPt.symm)
  have hs₁ := hs E₁ (ht₁.trans hPt.symm)
  rw [hAE, if_neg (Ne.symm hne), sub_zero] at hs₂
  rw [hAE, if_pos rfl] at hs₁
  have hF₂ : (0 : ℚ) < F E₂ := by exact_mod_cast hpos' E₂ ht₂
  have hs1 : s = 1 := by
    have : (F E₂ : ℚ) * (1 - s) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hF₂.ne'
    · linarith
  rw [hs1] at hs₁
  linarith

/-- **Fibres of a Mori fibre space of a surface over a curve are irreducible**: the relatively
ample divisor is positive on every contracted curve. -/
private theorem isIrreducible_fibre_of_isMoriFibreSpace {k : Type} [Field k] {V T : Scheme.{0}}
    (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T] (hdimV : topologicalKrullDim V = 2) (hQ : IsQFactorial sV)
    {K : Divisor V} {Δ : QDivisor V} {g : V ⟶ T} (hg : IsMoriFibreSpace sV sT K Δ g)
    (hdimT : topologicalKrullDim T = 1) (t : T) (ht : IsClosed ({t} : Set T)) :
    IsIrreducible (g.base ⁻¹' {t}) := by
  obtain ⟨hVv, hVproj⟩ := (Mori.isProjectiveVariety_iff k sV).mp hg.isProjectiveVariety
  have : IsProper sV := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hVproj).2
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have hgc := hg.isContraction
  obtain ⟨hTv, hTn⟩ := hgc.isNormalVariety_target
  have : IsNormal T := hTn
  have : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  have : IsSeparated sT := hTv.toIsSeparated
  have : QuasiCompact sT := hTv.toQuasiCompact
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsProper g :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hgc.isProjectiveMorphism).2
  obtain ⟨-, -, L, hL, -, hLa⟩ := hg.hasRelativelyAmpleMultiple
  have := hL.isInvertibleModule_divisorialSheaf
  exact isIrreducible_fibre sV sT g hdimV hQ hgc.comp_eq hgc.isIso_app hgc.surjective
    hg.relativePicardNumber_eq_one hdimT L hL (fun γ hγ =>
      MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple hVv g L.divisorialSheaf hLa γ hγ)
    t ht

/-- A `ℚ`-divisor numerically trivial over `T` has degree zero on every curve contracted to a
point of `T`. -/
private theorem intersectionNumber_eq_zero_of_isNumericallyTrivialOver {k : Type} [Field k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    (hQ : IsQFactorial sV) {g : V ⟶ T} {D : QDivisor V}
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sV g (QDivisor.toRDivisor D))
    (γ : ProperCurve sV) (hγ : γ.IsContractedBy g) :
    D.intersectionNumber k sV γ.ι γ.dim_le (isQCartier_of_isQFactorial sV hQ D) = 0 := by
  obtain ⟨m, hm, E, hE, hEc⟩ := (isQCartier_of_isQFactorial sV hQ D).exists_pos
  have hD : QDivisor.toRDivisor D =
      ∑ j : Fin 1, ![((m : ℝ))⁻¹] j • Divisor.toRDivisor (![E] j) := by
    rw [Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_zero,
      ← QDivisor.toRDivisor_toQDivisor, hE, map_zsmul, natCast_zsmul,
      ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (by positivity)]
  have h₁ : MMP.Flips.IsRIntersectionNumber k sV (QDivisor.toRDivisor D)
      ![((m : ℝ))⁻¹] ![E] γ (∑ j : Fin 1, ![((m : ℝ))⁻¹] j *
        ((fun _ : Fin 1 => E.degreeOn k sV γ.ι γ.dim_le hEc) j : ℝ)) := by
    refine ⟨fun j => by fin_cases j; exact hEc, fun _ => E.degreeOn k sV γ.ι γ.dim_le hEc,
      hD, fun j => ?_, rfl⟩
    fin_cases j
    exact MMP.Flips.isCartierIntersectionNumber_degreeOn (C := γ) (L := E) (hL := hEc)
  have h₂ : MMP.Flips.IsRIntersectionNumber k sV (0 : RDivisor V) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor V) γ 0 :=
    ⟨fun j => j.elim0, fun _ => 0, by simp, fun j => j.elim0, by simp⟩
  have h12 := hnum.2.2 γ hγ 1 _ _ _ 0 _ _ _ h₁ h₂
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero] at h12
  have hdeg : E.degreeOn k sV γ.ι γ.dim_le hEc = 0 := by
    exact_mod_cast (mul_eq_zero.mp h12).resolve_left (by positivity)
  rw [QDivisor.intersectionNumber_eq_of_smul k sV γ.ι γ.dim_le _ _ hm E hEc hE, hdeg]
  simp

/-- In a quasi-compact scheme, a point of height zero is closed. -/
private theorem isClosed_singleton_of_height_eq_zero {X : Scheme.{0}} [CompactSpace X] {x : X}
    (h : Order.height x = 0) : IsClosed ({x} : Set X) := by
  obtain ⟨c, hc, hcc⟩ := isClosed_closure.exists_closed_singleton (S := closure ({x} : Set X))
    ⟨x, subset_closure rfl⟩
  have hxc : x ⤳ c := specializes_iff_mem_closure.mpr hc
  have hle : c ≤ x := hxc
  have hmin := Order.height_eq_zero.mp h
  have hcx : c ⤳ x := hmin hle
  have : x = c := (inseparable_iff_specializes_and.mpr ⟨hxc, hcx⟩).eq
  rw [this]; exact hcc

/-- A closed subset of a Noetherian quasi-sober space all of whose points are closed is finite. -/
private theorem finite_of_isClosed_of_forall_isClosed {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    {S : Set X} (hS : IsClosed S) (h : ∀ z ∈ S, IsClosed ({z} : Set X)) : S.Finite := by
  classical
  obtain ⟨F, hF, hSF⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible ⟨S, hS⟩
  have hS' : S = ⋃ Z ∈ F, (Z : Set X) := by
    have := congrArg (fun C : TopologicalSpace.Closeds X => (C : Set X)) hSF
    simpa [TopologicalSpace.Closeds.coe_finset_sup] using this
  refine (Set.Finite.biUnion F.finite_toSet fun Z hZ => ?_).subset hS'.le
  obtain ⟨z, hz⟩ := QuasiSober.sober (hF ⟨Z, hZ⟩) Z.isClosed
  have hzS : z ∈ S := hS'.ge (Set.mem_iUnion₂.mpr ⟨Z, hZ, hz.mem⟩)
  have : (Z : Set X) = {z} := by rw [← hz.def, (h z hzS).closure_eq]
  exact (Set.finite_singleton z).subset this.le

/-- On an integral scheme of finite type over a field, the generic point of a prime divisor of a
surface has height one. -/
private theorem height_genericPoint_eq_one {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    (hdim : topologicalKrullDim X = 2) (P : Mori.PrimeDivisor X) :
    Order.height P.genericPoint = 1 := by
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := ‹LocallyOfFiniteType sX›
  have hpure : MMP.Intersection.IsPureDimensional X 2 := by
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [(Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq, hdim]
    rfl
  have h2 := MMP.Intersection.height_add_coheight_eq_of_isPureDimensional k hpure P.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P] at h2
  exact WithTop.add_right_cancel ENat.one_ne_top (h2.trans one_add_one_eq_two.symm)

/-- On a quasi-compact integral surface of finite type over a field, the points of a prime
divisor other than its generic point are closed. -/
private theorem isClosed_singleton_of_mem_support {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] [CompactSpace X]
    (hdim : topologicalKrullDim X = 2) (P : Mori.PrimeDivisor X) {z : X}
    (hz : z ∈ P.support) (hne : z ≠ P.genericPoint) : IsClosed ({z} : Set X) := by
  refine isClosed_singleton_of_height_eq_zero ?_
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hz
  have hsp : P.genericPoint ⤳ z := specializes_iff_mem_closure.mpr hz
  have hlt : z < P.genericPoint := lt_of_le_not_ge hsp fun h =>
    hne (inseparable_iff_specializes_and.mpr ⟨h, hsp⟩).eq
  have h1 := Order.height_add_one_le hlt
  rw [height_genericPoint_eq_one sX hdim P] at h1
  by_contra h
  have h2 : (1 : ℕ∞) + 1 ≤ Order.height z + 1 := by
    gcongr; exact ENat.one_le_iff_ne_zero.mpr h
  have h3 := h2.trans h1
  norm_num at h3

/-- On an integral scheme of dimension one, every point other than the generic point is
closed. -/
private theorem isClosed_singleton_of_ne_genericPoint {k : Type} [Field k] {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of k)) [IsIntegral T] [LocallyOfFiniteType sT] [CompactSpace T]
    (hdimT : topologicalKrullDim T = 1) {y : T} (hy : y ≠ genericPoint T) :
    IsClosed ({y} : Set T) := by
  refine isClosed_singleton_of_height_eq_zero ?_
  letI : T.Over (Spec (.of k)) := ⟨sT⟩
  have : LocallyOfFiniteType (T ↘ Spec (.of k)) := ‹LocallyOfFiniteType sT›
  have hpure : MMP.Intersection.IsPureDimensional T 1 := by
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [(Homeomorph.Set.univ T).isHomeomorph.topologicalKrullDim_eq, hdimT]
    rfl
  have h2 := MMP.Intersection.height_add_coheight_eq_of_isPureDimensional k hpure y
  rw [coheight_eq_one_of_ne_genericPoint hdimT hy] at h2
  have : Order.height y + 1 = 0 + 1 := by rw [h2]; simp
  exact WithTop.add_right_cancel ENat.one_ne_top this

/-- The generic points of an integral scheme. -/
private theorem mem_genericPoints_iff {X : Scheme.{0}} [IsIntegral X] {x : X} :
    x ∈ genericPoints X ↔ x = genericPoint X := by
  constructor
  · intro hx
    have h : closure ({x} : Set X) ∈ ({Set.univ} : Set (Set X)) :=
      (irreducibleComponents_eq_singleton (X := X)) ▸ hx
    exact IsGenericPoint.eq (show IsGenericPoint x Set.univ from h) (genericPoint_spec X)
  · rintro rfl
    show closure ({genericPoint X} : Set X) ∈ irreducibleComponents X
    rw [irreducibleComponents_eq_singleton, (genericPoint_spec X).def]
    rfl

/-- A local homomorphism between fields whose residue field map is an isomorphism is an
isomorphism. -/
private theorem isIso_stalkMap_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : f (genericPoint X) = genericPoint Y)
    (h : IsIso (f.residueFieldMap (genericPoint X))) : IsIso (f.stalkMap (genericPoint X)) := by
  have hres : ∀ (Z : Scheme.{0}) [IsIntegral Z] (z : Z), z = genericPoint Z →
      Function.Bijective (Z.residue z) := by
    intro Z _ z hz
    subst hz
    refine ⟨?_, Z.residue_surjective _⟩
    have hF : IsField (Z.presheaf.stalk (genericPoint Z)) :=
      Field.toIsField Z.functionField
    have hm := IsLocalRing.isField_iff_maximalIdeal_eq.mp hF
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.residue_eq_zero_iff a).mp ha
    rwa [hm] at this
  have hX := hres X (genericPoint X) rfl
  have hY := hres Y (f (genericPoint X)) hf
  have hR := (ConcreteCategory.isIso_iff_bijective _).mp h
  have hcomm := Scheme.residue_residueFieldMap f (genericPoint X)
  have h1 : Function.Bijective ((X.residue (genericPoint X)) ∘
      (f.stalkMap (genericPoint X))) := by
    have : ⇑(X.residue (genericPoint X)) ∘ ⇑(f.stalkMap (genericPoint X)) =
        ⇑(f.residueFieldMap (genericPoint X)) ∘ ⇑(Y.residue (f (genericPoint X))) := by
      funext a
      simpa using (congrArg (fun φ => (CommRingCat.Hom.hom φ) a) hcomm).symm
    rw [this]; exact hR.comp hY
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (Function.Bijective.of_comp_iff' hX _).mp h1

/-- **A finite birational map onto a normal curve.** Let `P` be a horizontal prime divisor of
generic degree one over a normal curve `T`, and `ν : N ⟶ V` a finite map from an integral
scheme onto `P`, an isomorphism on residue fields at the generic point. Then `ν ≫ g : N ⟶ T`
is an isomorphism. -/
private theorem isIso_comp_of_finrank_eq_one {k : Type} [Field k] {V T N : Scheme.{0}}
    (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [LocallyOfFiniteType sV] [CompactSpace V] [IsLocallyNoetherian V]
    [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T] [CompactSpace T]
    (hTv : Mori.IsVariety k sT) (hVv : Mori.IsVariety k sV)
    (hdimV : topologicalKrullDim V = 2) (hdimT : topologicalKrullDim T = 1)
    (g : V ⟶ T) [IsProper g] (hgs : g ≫ sT = sV)
    (P : Mori.PrimeDivisor V) (hP : g P.genericPoint = genericPoint T)
    (hdeg : letI := (g.residueFieldMap P.genericPoint).hom.toAlgebra
      Module.finrank (T.residueField (g P.genericPoint)) (V.residueField P.genericPoint) = 1)
    [IsIntegral N] (ν : N ⟶ V) [IsFinite ν] (hrange : Set.range ν.base = (P.support : Set V))
    (hres : IsIso (ν.residueFieldMap (genericPoint N))) : IsIso (ν ≫ g) := by
  classical
  have : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  -- the generic point of `N` maps to that of `P`
  have hνη : ν (genericPoint N) = P.genericPoint := by
    have hP' : P.genericPoint ∈ Set.range ν.base := by
      rw [hrange, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    obtain ⟨x, hx⟩ := hP'
    have h1 : ν (genericPoint N) ⤳ P.genericPoint := by
      rw [← hx]; exact ((genericPoint_spec N).specializes trivial).map ν.continuous
    have h2 : P.genericPoint ⤳ ν (genericPoint N) := by
      have : ν (genericPoint N) ∈ (P.support : Set V) := hrange ▸ ⟨_, rfl⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    exact (inseparable_iff_specializes_and.mpr ⟨h1, h2⟩).eq
  have hhη : (ν ≫ g) (genericPoint N) = genericPoint T := by
    rw [Scheme.Hom.comp_apply, hνη, hP]
  -- the residue field map of the composite is an isomorphism
  have hgres : ∀ y (hy : y = P.genericPoint), IsIso (g.residueFieldMap y) := by
    rintro y rfl
    letI := (g.residueFieldMap P.genericPoint).hom.toAlgebra
    have hb := Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdeg
    exact (ConcreteCategory.isIso_iff_bijective _).mpr hb
  have hres' : IsIso ((ν ≫ g).residueFieldMap (genericPoint N)) := by
    rw [Scheme.residueFieldMap_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hgres _ hνη) hres
  -- `ν ≫ g` is birational
  have hbir : IsBirational (ν ≫ g) := by
    refine ⟨⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩, fun x hx => ?_⟩
    · rw [mem_genericPoints_iff] at hx ⊢
      rw [hx]; exact hhη
    · rw [mem_genericPoints_iff] at hx hy
      rw [hx, hy]
    · rw [mem_genericPoints_iff] at hy
      exact ⟨genericPoint N, mem_genericPoints_iff.mpr rfl, hhη.trans hy.symm⟩
    · rw [mem_genericPoints_iff] at hx
      subst hx
      exact isIso_stalkMap_genericPoint (ν ≫ g) hhη hres'
  -- `ν ≫ g` has finite fibres
  have : LocallyOfFiniteType (g ≫ sT) := by rw [hgs]; exact hVv.toLocallyOfFiniteType
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g sT
  have hfib : ∀ y : T, ((ν ≫ g).base ⁻¹' {y}).Finite := by
    intro y
    by_cases hy : y = genericPoint T
    · subst hy
      refine (ν.finite_preimage_singleton P.genericPoint).subset fun x hx => ?_
      have hx' : g (ν x) = genericPoint T := hx
      have hmem : ν x ∈ (P.support : Set V) := hrange ▸ ⟨x, rfl⟩
      by_contra hne
      have hcl := isClosed_singleton_of_mem_support sV hdimV P hmem hne
      have := g.isClosedMap _ hcl
      rw [Set.image_singleton, hx'] at this
      exact not_isClosed_genericPoint hdimT this
    · have hycl := isClosed_singleton_of_ne_genericPoint sT hdimT hy
      have : IsNoetherian V := {}
      set S : Set V := g.base ⁻¹' {y} ∩ (P.support : Set V)
      have hS : S.Finite := by
        refine finite_of_isClosed_of_forall_isClosed
          ((hycl.preimage g.continuous).inter P.idealSheaf.support.isClosed) fun z hz => ?_
        refine isClosed_singleton_of_mem_support sV hdimV P hz.2 fun h => ?_
        have : g z = y := hz.1
        rw [h, hP] at this
        exact hy this.symm
      refine (hS.biUnion fun z _ => ν.finite_preimage_singleton z).subset fun x hx => ?_
      refine Set.mem_iUnion₂.mpr ⟨ν x, ⟨hx, hrange ▸ ⟨x, rfl⟩⟩, rfl⟩
  have : LocallyQuasiFinite (ν ≫ g) :=
    (locallyQuasiFinite_iff_finite_preimage_singleton).mpr hfib
  have : IsFinite (ν ≫ g) :=
    IsFinite.of_isProper_of_locallyQuasiFinite (ν ≫ g)
  have hNv : Mori.IsVariety k (ν ≫ sV) := by
    have := hVv.toIsSeparated
    have := hVv.toLocallyOfFiniteType
    have := hVv.toQuasiCompact
    exact ⟨⟩
  have hbm : IsBirationalMorphism (ν ≫ g) := by
    haveI : Finite (irreducibleComponents N) := by
      rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
    haveI : Finite (irreducibleComponents T) := by
      rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
    obtain ⟨U, W, hUW, hU, hW, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational (ν ≫ g)
      hbir (Or.inl ⟨inferInstance, inferInstance⟩)
    exact MMP.Flips.isBirationalMorphism_of_isIso_resLE (ν ≫ g) U W hU.nonempty hW.nonempty hUW
      hiso
  exact (MMP.Mori.isOpenImmersion_and_isIso_of_locallyQuasiFinite_of_isBirationalMorphism
    (ν ≫ sV) sT hNv ⟨hTv, inferInstance⟩ (ν ≫ g) (by rw [Category.assoc, hgs])
    hbm).2 inferInstance

/-- **The generic fibre degree at a general closed fibre.** For every `ℚ`-divisor `D`, over a
dense open of `T` every closed fibre is a proper curve `C`, the whole fibre, with
`deg_{k(T)} D|_{V_η} = (D · C)`. -/
private theorem exists_dense_open_genericFiberDegree_eq
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T]
    (hdimV : topologicalKrullDim V = 2) (hQ : IsQFactorial sV)
    (g : V ⟶ T) [IsDominant g] {K : Divisor V} {Δ : QDivisor V}
    (hg : IsMoriFibreSpace sV sT K Δ g) (hdimT : topologicalKrullDim T = 1) (D : QDivisor V) :
    ∃ U : T.Opens, Dense (U : Set T) ∧ ∀ w ∈ U,
      IsClosed ({w} : Set T) → ∃ C : ProperCurve sV, C.IsContractedBy g ∧ g C.point = w ∧
        closure {C.point} = g.base ⁻¹' {w} ∧
        MMP.Flips.genericFiberDegree g D = D.intersectionNumber k sV C.ι C.dim_le
          (isQCartier_of_isQFactorial sV hQ D) := by
  classical
  obtain ⟨hVv, hVproj⟩ := (Mori.isProjectiveVariety_iff k sV).mp hg.isProjectiveVariety
  have : IsProper sV := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hVproj).2
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have : IsSeparated sV := hVv.toIsSeparated
  have hgc := hg.isContraction
  obtain ⟨hTv, hTn⟩ := hgc.isNormalVariety_target
  have : IsNormal T := hTn
  have : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  have : IsSeparated sT := hTv.toIsSeparated
  have : QuasiCompact sT := hTv.toQuasiCompact
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsProper g :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hgc.isProjectiveMorphism).2
  have : Surjective g := ⟨hgc.surjective⟩
  obtain ⟨U, hU, h⟩ := MMP.Flips.exists_dense_open_genericFiberDegree_eq_sum_intersectionNumber
    sV sT g hgc.comp_eq (by rw [hdimV, hdimT]; rfl) D (isQCartier_of_isQFactorial sV hQ D)
  refine ⟨U, hU, fun w hw hwc => ?_⟩
  obtain ⟨S, hS, hsum⟩ := (h w hw).2 hwc
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober
    (isIrreducible_fibre_of_isMoriFibreSpace sV sT hdimV hQ hg hdimT w hwc) (hwc.preimage g.continuous)
  have hξw : g ξ = w := hξ.mem
  have hmax : {x : V | g x = w ∧ ∀ y : V, g y = w → y ⤳ x → y = x} = {ξ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hmx⟩
      have : x ∈ closure ({ξ} : Set V) := by rw [hξ.def]; exact hx
      exact (hmx ξ hξw (specializes_iff_mem_closure.mpr this)).symm
    · rintro rfl
      refine ⟨hξw, fun y hy hyx => ?_⟩
      have : y ∈ closure ({x} : Set V) := by rw [hξ.def]; exact hy
      exact (inseparable_iff_specializes_and.mpr
        ⟨hyx, specializes_iff_mem_closure.mpr this⟩).eq
  rw [hmax] at hS
  obtain ⟨C, hCS, hCξ⟩ : ∃ C ∈ S, C.point = ξ := by
    have : ξ ∈ ProperCurve.point '' (S : Set (ProperCurve sV)) := by rw [hS]; rfl
    obtain ⟨C, hC, h⟩ := this
    exact ⟨C, hC, h⟩
  have hSeq : S = {C} := by
    ext C'
    simp only [Finset.mem_singleton]
    refine ⟨fun hC' => ?_, fun h => h ▸ hCS⟩
    have : C'.point ∈ ({ξ} : Set V) := hS ▸ ⟨C', hC', rfl⟩
    exact ProperCurve.ext (this.trans hCξ.symm)
  rw [hSeq, Finset.sum_singleton] at hsum
  have hcl : closure {C.point} = g.base ⁻¹' {w} := by rw [hCξ]; exact hξ.def
  refine ⟨C, fun x hx => ?_, hCξ ▸ hξw, hcl, hsum⟩
  rw [hcl] at hx
  have : g x = w := hx
  rw [this, hCξ, hξw]

/-- On a normal surface, the points outside the smooth locus are closed. -/
private theorem isClosed_singleton_of_notMem_smoothLocus {k : Type} [Field k] [PerfectField k]
    {V : Scheme.{0}} (sV : V ⟶ Spec (.of k)) [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [CompactSpace V] (hVv : Mori.IsVariety k sV) (hdimV : topologicalKrullDim V = 2) {x : V}
    (hx : x ∉ Mori.smoothLocus sV) : IsClosed ({x} : Set V) := by
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  refine isClosed_singleton_of_height_eq_zero ?_
  letI : V.Over (Spec (.of k)) := ⟨sV⟩
  have : LocallyOfFiniteType (V ↘ Spec (.of k)) := ‹LocallyOfFiniteType sV›
  have hpure : MMP.Intersection.IsPureDimensional V 2 := by
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [(Homeomorph.Set.univ V).isHomeomorph.topologicalKrullDim_eq, hdimV]
    rfl
  have h2 := MMP.Intersection.height_add_coheight_eq_of_isPureDimensional k hpure x
  have hc0 : Order.coheight x ≠ 0 := by
    intro h0
    have hmax := Order.coheight_eq_zero.mp h0
    have hle : x ≤ genericPoint V := (genericPoint_spec V).specializes trivial
    have hge : genericPoint V ≤ x := hmax hle
    have : x = genericPoint V := (inseparable_iff_specializes_and.mpr ⟨hge, hle⟩).eq
    exact hx (this ▸ MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus')
  have hc1 : Order.coheight x ≠ 1 := by
    intro h1
    have := MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus ⟨hVv, inferInstance⟩
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1)
    have heq : Mori.PrimeDivisor.genericPoint (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1) =
        x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    rw [heq] at this
    exact hx this
  have h2' : (2 : ℕ∞) ≤ Order.coheight x := by
    generalize Order.coheight x = c at hc0 hc1 ⊢
    induction c using ENat.recTopCoe with
    | top => exact le_top
    | coe c =>
      have : c ≠ 0 := fun h => hc0 (by simp [h])
      have : c ≠ 1 := fun h => hc1 (by simp [h])
      exact_mod_cast (by omega : 2 ≤ c)
  by_contra hne
  have h1 : (1 : ℕ∞) ≤ Order.height x := ENat.one_le_iff_ne_zero.mpr hne
  have : (1 : ℕ∞) + 2 ≤ Order.height x + Order.coheight x := add_le_add h1 h2'
  rw [h2] at this
  norm_num at this

/-- In a scheme of finite type over a field, every nonempty open contains a closed point. -/
private theorem exists_isClosed_mem_of_isOpen {k : Type} [Field k] {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of k)) [LocallyOfFiniteType sT] {W : Set T} (hW : IsOpen W)
    (hne : W.Nonempty) : ∃ w ∈ W, IsClosed ({w} : Set T) := by
  have := LocallyOfFiniteType.jacobsonSpace sT
  obtain ⟨w, hwW, hw⟩ := nonempty_inter_closedPoints hne hW.isLocallyClosed
  exact ⟨w, hwW, hw⟩

/-- **Intersection numbers on a dense open.** For a `ℚ`-Cartier `ℚ`-divisor `L` on a normal
integral scheme `X`, a dense open `U` and a curve `i : Z ⟶ U`, `(L|_U · Z) = (L · Z)`. -/
private theorem intersectionNumber_restrictOpen_eq {k : Type} [Field k] {X Z : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [QuasiCompact sX] (U : X.Opens) [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
    [CompactSpace U] [IsDominant U.ι] [QuasiCompact (U.ι ≫ sX)]
    (i : Z ⟶ U) [IsProper (i ≫ U.ι ≫ sX)] [IsProper ((i ≫ U.ι) ≫ sX)]
    (hdim : topologicalKrullDim Z ≤ 1)
    (L : QDivisor X) (hL : L.IsQCartier) (hLU : QDivisor.IsQCartier (DivisorWithCoeffs.restrictOpen U L)) :
    QDivisor.intersectionNumber k (U.ι ≫ sX) i hdim (DivisorWithCoeffs.restrictOpen U L) hLU =
      L.intersectionNumber k sX (i ≫ U.ι) hdim hL := by
  have hm := QDivisor.cartierIndex_pos hL
  obtain ⟨N, hN, hNc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hL
  obtain ⟨N', hN'⟩ := hNc.exists_isPullback (f := U.ι)
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant U.ι N)
  have hiso : ∀ P : Mori.PrimeDivisor U, IsIso (U.ι.stalkMap P.genericPoint) := fun P =>
    inferInstanceAs <| IsIso (U.ι.toLRSHom.stalkMap P.genericPoint)
  have hNN' : N' = (DivisorWithCoeffs.restrictOpen U N) := by
    ext P
    rw [DivisorWithCoeffs.coeff_restrictOpen]
    exact MMP.Positivity.coeff_eq_of_isPullback P _
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P).symm hNc hN'
  have hp := hNN' ▸ hN'
  have hNUc : Divisor.IsCartier ((DivisorWithCoeffs.restrictOpen U N)) := Divisor.IsPullback.isCartier hp hNc
  have hNU : Divisor.toQDivisor ((DivisorWithCoeffs.restrictOpen U N)) =
      ((L.cartierIndex hL : ℕ) : ℤ) • (DivisorWithCoeffs.restrictOpen U L) := by
    ext P
    exact congrArg (fun G : QDivisor X => G (OpenWeilRestriction.primeDivisorMap U.ι P)) hN
  rw [QDivisor.intersectionNumber_eq_of_smul k (U.ι ≫ sX) i hdim _ hLU hm _ hNUc hNU,
    QDivisor.intersectionNumber_eq_of_smul k sX (i ≫ U.ι) hdim _ hL hm _ hNc hN]
  congr 2
  have := hNc.isInvertibleModule_divisorialSheaf
  have := hNUc.isInvertibleModule_divisorialSheaf
  change Mori.degreeOn k (U.ι ≫ sX) i hdim (Divisor.divisorialSheaf ((DivisorWithCoeffs.restrictOpen U N))) =
    Mori.degreeOn k sX (i ≫ U.ι) hdim N.divisorialSheaf
  rw [degreeOn_eq_of_iso k (U.ι ≫ sX) i hdim
      (Divisor.IsPullback.divisorialSheafIso (hBc := hNc) hp),
    degreeOn_pullback_eq_degreeOn_comp (U.ι ≫ sX) sX U.ι i rfl]

/-- The intersection number along a curve is unchanged by an isomorphism of curves over `X`. -/
private theorem intersectionNumber_eq_of_iso_comp {k : Type} [Field k] {X C C' : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]
    (i : C ⟶ X) (i' : C' ⟶ X) [IsProper (i ≫ sX)] [IsProper (i' ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) (hdim' : topologicalKrullDim C' ≤ 1) (e : C ≅ C')
    (he : e.hom ≫ i' = i) (L : QDivisor X) (hL : L.IsQCartier) :
    L.intersectionNumber k sX i hdim hL = L.intersectionNumber k sX i' hdim' hL := by
  obtain ⟨m, hm, N, hN, hNc⟩ := hL.exists_pos
  rw [QDivisor.intersectionNumber_eq_of_smul k sX i hdim _ hL hm _ hNc hN,
    QDivisor.intersectionNumber_eq_of_smul k sX i' hdim' _ hL hm _ hNc hN]
  congr 2
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hNc.isInvertibleModule_divisorialSheaf
  exact MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX i i' hdim hdim' e he
    N.divisorialSheaf

/-- **The canonical degree of a fibre in the smooth locus.** If a prime divisor `E` of a normal
proper surface lies in the smooth locus and `(E · E) = 0`, then `(K · E) ≥ -2`, and if
`(K · E) = -2` then `E ≅ ℙ¹_k` over `k`: by adjunction `((K + E) · E) = 2 p_a(E) - 2`. -/
private theorem neg_two_le_intersectionNumber_canonical {k : Type} [Field k] [IsAlgClosed k]
    {V : Scheme.{0}} (sV : V ⟶ Spec (.of k)) [IsIntegral V] [CompactSpace V]
    [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV] [IsProper sV]
    (hVv : Mori.IsVariety k sV) (hQ : IsQFactorial sV)
    (K : Divisor V) (hK : K.IsCanonicalDivisor sV 2) (E : Mori.PrimeDivisor V)
    (hE : E.support ⊆ Mori.smoothLocus sV) (C : ProperCurve sV) (hC : C.point = E.genericPoint)
    (hEE : (Divisor.toQDivisor (Finsupp.single E 1)).intersectionNumber k sV C.ι C.dim_le
      (isQCartier_of_isQFactorial sV hQ _) = 0) :
    -2 ≤ (Divisor.toQDivisor K).intersectionNumber k sV C.ι C.dim_le
      (isQCartier_of_isQFactorial sV hQ _) ∧
    ((Divisor.toQDivisor K).intersectionNumber k sV C.ι C.dim_le
      (isQCartier_of_isQFactorial sV hQ _) = -2 →
      ∃ e : projectiveLine k ≅ C.scheme, e.hom ≫ C.ι ≫ sV = projectiveLine k ↘ Spec (.of k)) := by
  classical
  obtain ⟨p, hpC⟩ := C
  change p = E.genericPoint at hC
  subst hC
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have : IsSeparated sV := hVv.toIsSeparated
  have : IsNoetherian V := {}
  set U : V.Opens := Mori.smoothLocus sV
  have hgE : E.genericPoint ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hηU : E.genericPoint ∈ U := hE hgE
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have : IsDominant U.ι := AlgebraicGeometry.Opens.isDominant_ι (U.isOpen.dense ⟨_, hηU⟩)
  have : CompactSpace U :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set V))
  have : QuasiCompact (U.ι ≫ sV) := inferInstance
  have hUv : Mori.IsVariety k (U.ι ≫ sV) := ⟨⟩
  have hUs : Mori.IsSmoothScheme (U.ι ≫ sV) := by
    unfold Mori.IsSmoothScheme
    rw [Mori.smoothLocus_eq_smoothLocus, ← Scheme.Hom.preimage_smoothLocus_eq,
      ← Mori.smoothLocus_eq_smoothLocus, Scheme.Opens.ι_preimage_self]
  have hK' := Divisor.IsCanonicalDivisor.restrictOpen ⟨hVv, inferInstance⟩ hK U
  have hUd : topologicalKrullDim U = 2 := hK'.1
  -- the prime divisor `E'` of `U` with closure `E`
  obtain ⟨E', hE'⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff U.ι E).mpr
    ⟨⟨_, hηU⟩, rfl⟩
  have hE'η : U.ι E'.genericPoint = E.genericPoint := by
    rw [← OpenWeilRestriction.genericPoint_primeDivisorMap, hE']
  set D' : Divisor U := Finsupp.single E' 1
  have hD'1 : ∀ E'' ∈ D'.support, D' E'' = 1 := by
    intro E'' h
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h
    subst h; simp [D']
  have hsupp : D'.suppIdeal =
      Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure ({E'.genericPoint} : Set U)) := by
    rw [DivisorWithCoeffs.suppIdeal]
    congr 1
    apply TopologicalSpace.Closeds.ext
    rw [TopologicalSpace.Closeds.coe_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure E',
      DivisorWithCoeffs.coe_supp, Finsupp.support_single_ne_zero _ one_ne_zero]
    simp
  obtain ⟨e₁, he₁⟩ := MMP.Threefold.Resolution.exists_subscheme_iso_of_eq hsupp
  have hcl : closure ({E.genericPoint} : Set V) ⊆ Set.range U.ι := by
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure, Scheme.Opens.range_ι]; exact hE
  obtain ⟨e₂, he₂⟩ := MMP.Threefold.Resolution.exists_curveSubschemeAt_iso U.ι E'.genericPoint
    hE'η hcl
  set i := D'.suppIdeal.subschemeι
  have he : (e₁ ≪≫ e₂).hom ≫ curveSubschemeAtι E.genericPoint = i ≫ U.ι := by
    simp only [Iso.trans_hom, Category.assoc, he₂]
    rw [← Category.assoc, he₁]
  have hprop : IsProper (D'.suppIdeal.subschemeι ≫ U.ι ≫ sV) := by
    rw [← Category.assoc, ← he, Category.assoc]; infer_instance
  have hprop' : IsProper ((i ≫ U.ι) ≫ sV) := by rw [Category.assoc]; exact hprop
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
    (D'.suppIdeal.subschemeι ≫ U.ι ≫ sV)
  have h : IsIntersectionNumber (U.ι ≫ sV)
      (Divisor.toQDivisor ((DivisorWithCoeffs.restrictOpen U K) + D')) D'.suppIdeal
      (-2 * eulerCharacteristic k (D'.suppIdeal.subschemeι ≫ U.ι ≫ sV)
        (SheafOfModules.unit D'.suppIdeal.subscheme.ringCatSheaf)) :=
    MMP.Threefold.isIntersectionNumber_canonical_add_eq_neg_two_mul_eulerCharacteristic
      hUv hUs hUd hK' D' hD'1 hprop
  obtain ⟨hpr, hdim, hD, hval⟩ := h
  -- the arithmetic genus of the curve is nonnegative
  have : IsIntegral D'.suppIdeal.subscheme := by
    rw [hsupp]
    exact StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  have hg := (arithmeticGenus_eq_finrank_cohomologyOverField_one
    (D'.suppIdeal.subschemeι ≫ U.ι ≫ sV) hdim).2.2
  unfold arithmeticGenus at hg
  -- transfer to `V`
  have hKE : Divisor.toQDivisor ((DivisorWithCoeffs.restrictOpen U K) + D') =
      DivisorWithCoeffs.restrictOpen U (Divisor.toQDivisor (K + Finsupp.single E 1)) := by
    ext P
    change DivisorWithCoeffs.coeff (Divisor.toQDivisor ((DivisorWithCoeffs.restrictOpen U K) + D')) P =
      DivisorWithCoeffs.coeff (Divisor.toQDivisor (K + Finsupp.single E 1))
        (OpenWeilRestriction.primeDivisorMap U.ι P)
    rw [Divisor.coeff_toQDivisor, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_restrictOpen]
    congr 2
    by_cases hP : P = E'
    · subst hP
      rw [hE', DivisorWithCoeffs.coeff_single_self, DivisorWithCoeffs.coeff_single_self]
    · have hP' : OpenWeilRestriction.primeDivisorMap U.ι P ≠ E := fun h' =>
        hP (OpenWeilRestriction.primeDivisorMap_injective U.ι (h'.trans hE'.symm))
      rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hP),
        DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hP')]
  have hqc : ∀ D : QDivisor V, D.IsQCartier := isQCartier_of_isQFactorial sV hQ
  have h1 := intersectionNumber_restrictOpen_eq sV U i hdim
    (Divisor.toQDivisor (K + Finsupp.single E 1)) (hqc _) (hKE ▸ hD)
  have h2 := intersectionNumber_eq_of_iso_comp sV (i ≫ U.ι) (curveSubschemeAtι E.genericPoint)
    hdim (ProperCurve.dim_le ⟨E.genericPoint, hpC⟩) (e₁ ≪≫ e₂) he
    (Divisor.toQDivisor (K + Finsupp.single E 1)) (hqc _)
  have h3 : (Divisor.toQDivisor ((DivisorWithCoeffs.restrictOpen U K) + D')).intersectionNumber k (U.ι ≫ sV) i hdim
      hD = QDivisor.intersectionNumber k (U.ι ≫ sV) i hdim
        (DivisorWithCoeffs.restrictOpen U (Divisor.toQDivisor (K + Finsupp.single E 1)))
        (hKE ▸ hD) := by
    congr 1
  rw [h3, h1, h2] at hval
  have hadd := QDivisor.intersectionNumber_add' k sV (curveSubschemeAtι E.genericPoint)
    (ProperCurve.dim_le ⟨E.genericPoint, hpC⟩) (Divisor.toQDivisor K)
    (Divisor.toQDivisor (Finsupp.single E 1)) (hqc _) (hqc _) (hqc _)
  have h4 : Divisor.toQDivisor (K + Finsupp.single E 1) =
      Divisor.toQDivisor K + Divisor.toQDivisor (Finsupp.single E 1) := map_add _ _ _
  rw [intersectionNumber_congr sV _ _ (hqc _) (hqc _) h4] at hval
  rw [hadd] at hval
  change _ + (Divisor.toQDivisor (Finsupp.single E 1)).intersectionNumber k sV
    (ProperCurve.ι ⟨E.genericPoint, hpC⟩) _ _ = _ at hval
  rw [hEE] at hval
  change -2 ≤ (Divisor.toQDivisor K).intersectionNumber k sV
    (ProperCurve.ι ⟨E.genericPoint, hpC⟩) _ _ ∧
    ((Divisor.toQDivisor K).intersectionNumber k sV (ProperCurve.ι ⟨E.genericPoint, hpC⟩) _ _ = -2 →
      ∃ e : projectiveLine k ≅ curveSubschemeAt E.genericPoint,
        e.hom ≫ curveSubschemeAtι E.genericPoint ≫ sV = projectiveLine k ↘ Spec (.of k))
  have : (eulerCharacteristic k (D'.suppIdeal.subschemeι ≫ U.ι ≫ sV)
      (SheafOfModules.unit D'.suppIdeal.subscheme.ringCatSheaf) : ℚ) ≤ 1 := by
    have : eulerCharacteristic k (D'.suppIdeal.subschemeι ≫ U.ι ≫ sV)
        (SheafOfModules.unit D'.suppIdeal.subscheme.ringCatSheaf) ≤ 1 := by linarith
    exact_mod_cast this
  refine ⟨by linarith, fun hK2 => ?_⟩
  -- the arithmetic genus vanishes, so the curve is a projective line
  have hχ : eulerCharacteristic k (D'.suppIdeal.subschemeι ≫ U.ι ≫ sV)
      (SheafOfModules.unit D'.suppIdeal.subscheme.ringCatSheaf) = 1 := by
    have : (eulerCharacteristic k (D'.suppIdeal.subschemeι ≫ U.ι ≫ sV)
        (SheafOfModules.unit D'.suppIdeal.subscheme.ringCatSheaf) : ℚ) = 1 := by linarith
    exact_mod_cast this
  have hpa : arithmeticGenus (D'.suppIdeal.subschemeι ≫ U.ι ≫ sV) = 0 := by
    unfold arithmeticGenus; rw [hχ]; norm_num
  have hdim1 : topologicalKrullDim D'.suppIdeal.subscheme = 1 := by
    rw [(Scheme.homeoOfIso (e₁ ≪≫ e₂)).isHomeomorph.topologicalKrullDim_eq]
    exact hpC.dim_eq
  haveI : IsProper (D'.suppIdeal.subschemeι ≫ U.ι ≫ sV) := hprop
  obtain ⟨e', he'⟩ := ((MMP.Mori.arithmeticGenus_nonneg_and_eq_zero_iff
    (D'.suppIdeal.subschemeι ≫ U.ι ≫ sV) hdim1).2).mp hpa
  refine ⟨e' ≪≫ (e₁ ≪≫ e₂), ?_⟩
  calc (e' ≪≫ (e₁ ≪≫ e₂)).hom ≫ curveSubschemeAtι E.genericPoint ≫ sV
      = e'.hom ≫ ((e₁ ≪≫ e₂).hom ≫ curveSubschemeAtι E.genericPoint) ≫ sV := by
        simp only [Iso.trans_hom, Category.assoc]
    _ = e'.hom ≫ (i ≫ U.ι) ≫ sV := by rw [he]
    _ = projectiveLine k ↘ Spec (.of k) := by rw [← he']; simp only [Category.assoc, i]

/-- The generic point of a proper curve is not a closed point. -/
private theorem not_isClosed_singleton_point {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) : ¬ IsClosed ({C.point} : Set X) := by
  intro h
  have h1 := MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq C.point
  rw [h.closure_eq] at h1
  have h2 : topologicalKrullDim (curveSubschemeAt C.point) = 1 := C.dim_eq
  rw [h1] at h2
  have : DiscreteTopology ({C.point} : Set X) := Subsingleton.discreteTopology
  have h3 := topologicalKrullDim_zero_of_discreteTopology ({C.point} : Set X)
  rw [h2] at h3
  exact absurd h3 (by decide)

open Classical in
/-- The coefficients of a prime divisor viewed as a `ℚ`-divisor. -/
private theorem toQDivisor_single_apply {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (P E : Mori.PrimeDivisor X) :
    Divisor.toQDivisor (Finsupp.single P 1) E = if E = P then 1 else 0 := by
  change DivisorWithCoeffs.coeff (Divisor.toQDivisor (Finsupp.single P 1)) E = _
  rw [Divisor.coeff_toQDivisor]
  by_cases h : E = P
  · subst h; rw [DivisorWithCoeffs.coeff_single_self, if_pos rfl]; simp
  · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm h), if_neg h]; simp

/-- The generic fibre degree of a horizontal prime divisor is its generic degree. -/
private theorem genericFiberDegree_single {V T : Scheme.{0}} [IsIntegral V] [IsIntegral T]
    [IsLocallyNoetherian V] [IsNormal V] (g : V ⟶ T) (P : Mori.PrimeDivisor V)
    (hP : g.base P.genericPoint = genericPoint T) :
    MMP.Flips.genericFiberDegree g (Divisor.toQDivisor (Finsupp.single P 1)) =
      (letI := (g.residueFieldMap P.genericPoint).hom.toAlgebra
      Module.finrank (T.residueField (g.base P.genericPoint)) (V.residueField P.genericPoint)) := by
  classical
  set DP : QDivisor V := Divisor.toQDivisor (Finsupp.single P 1)
  have hDPcoeff : ∀ E, DP E = if E = P then 1 else 0 := toQDivisor_single_apply P
  unfold MMP.Flips.genericFiberDegree
  have hsupp : DP.support = {P} := by
    ext E
    rw [Finsupp.mem_support_iff, Finset.mem_singleton]
    constructor
    · intro h; by_contra h'; exact h (by rw [hDPcoeff, if_neg h'])
    · rintro rfl; rw [hDPcoeff, if_pos rfl]; norm_num
  rw [hsupp, Finset.sum_singleton]
  change DP P * _ = _
  rw [hDPcoeff, if_pos rfl, one_mul]
  simp only [MMP.Flips.genericFiberPointDegree]
  rw [if_pos hP]

/-- **Horizontal prime divisors have positive generic degree.** -/
private theorem one_le_genericFiberPointDegree
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T]
    (hdimV : topologicalKrullDim V = 2) (hQ : IsQFactorial sV)
    (g : V ⟶ T) [IsDominant g] {K : Divisor V} {Δ : QDivisor V}
    (hg : IsMoriFibreSpace sV sT K Δ g) (hdimT : topologicalKrullDim T = 1)
    (P : Mori.PrimeDivisor V) (hP : g.base P.genericPoint = genericPoint T) :
    1 ≤ MMP.Flips.genericFiberPointDegree g P := by
  classical
  obtain ⟨hVv, hVproj⟩ := (Mori.isProjectiveVariety_iff k sV).mp hg.isProjectiveVariety
  have : IsProper sV := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hVproj).2
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have hgc := hg.isContraction
  obtain ⟨hTv, hTn⟩ := hgc.isNormalVariety_target
  have : IsNormal T := hTn
  have : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  have : QuasiCompact sT := hTv.toQuasiCompact
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsProper g :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hgc.isProjectiveMorphism).2
  have hqc : ∀ D : QDivisor V, D.IsQCartier := isQCartier_of_isQFactorial sV hQ
  set DP : QDivisor V := Divisor.toQDivisor (Finsupp.single P 1)
  have hDPcoeff : ∀ E, DP E = if E = P then 1 else 0 := toQDivisor_single_apply P
  have hDP0 : 0 ≤ DP := fun E => by
    change (0 : ℚ) ≤ DP E
    rw [hDPcoeff]; split_ifs <;> norm_num
  have hDPsupp : ∀ x, x ∈ DP.supp ↔ x ∈ P.support := fun x => by
    rw [DivisorWithCoeffs.mem_supp_iff]
    constructor
    · rintro ⟨E, hE, hxE⟩
      have : E = P := by
        by_contra h
        apply hE
        change DP E = 0
        rw [hDPcoeff, if_neg h]
      exact this ▸ hxE
    · intro hx
      refine ⟨P, ?_, hx⟩
      change DP P ≠ 0
      rw [hDPcoeff, if_pos rfl]; norm_num
  obtain ⟨U, hU, hUw⟩ := exists_dense_open_genericFiberDegree_eq sV sT hdimV hQ g hg hdimT DP
  obtain ⟨w, hwU, hwc⟩ := exists_isClosed_mem_of_isOpen sT U.isOpen hU.nonempty
  obtain ⟨C, hCc, hCw, hcl, hgd⟩ := hUw w hwU hwc
  have hwne : w ≠ genericPoint T := fun h => not_isClosed_genericPoint hdimT (h ▸ hwc)
  have hnotin : C.point ∉ DP.supp := by
    rw [hDPsupp]
    intro hmem
    by_cases hη : C.point = P.genericPoint
    · exact hwne (by rwa [← hCw, hη])
    · exact not_isClosed_singleton_point C
        (isClosed_singleton_of_mem_support sV hdimV P hmem hη)
  obtain ⟨hnn, hiff⟩ := intersectionNumber_nonneg_and_eq_zero_iff sV DP (hqc _) hDP0 C hnotin
  have hmeet : ∃ x, C.point ⤳ x ∧ x ∈ DP.supp := by
    have himg : g.base '' P.support = Set.univ := by
      have hcl' : IsClosed (g.base '' P.support) :=
        g.isClosedMap _ P.idealSheaf.support.isClosed
      have hη : genericPoint T ∈ g.base '' P.support := by
        refine ⟨P.genericPoint, ?_, hP⟩
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      refine Set.eq_univ_of_forall fun y => ?_
      have : y ∈ closure ({genericPoint T} : Set T) := by
        rw [(genericPoint_spec T).def]; trivial
      exact closure_minimal (Set.singleton_subset_iff.mpr hη) hcl' this
    obtain ⟨x, hxP, hxw⟩ : w ∈ g.base '' P.support := himg ▸ trivial
    refine ⟨x, ?_, (hDPsupp x).mpr hxP⟩
    have : x ∈ closure ({C.point} : Set V) := by rw [hcl]; exact hxw
    exact specializes_iff_mem_closure.mpr this
  have hposP : 0 < DP.intersectionNumber k sV C.ι C.dim_le (hqc _) := by
    refine lt_of_le_of_ne hnn fun h => ?_
    obtain ⟨x, hx, hxs⟩ := hmeet
    exact hiff.mp h.symm x hx hxs
  rw [← hgd, genericFiberDegree_single g P hP] at hposP
  have : 0 < (letI := (g.residueFieldMap P.genericPoint).hom.toAlgebra
      Module.finrank (T.residueField (g.base P.genericPoint)) (V.residueField P.genericPoint)) := by
    exact_mod_cast hposP
  simp only [MMP.Flips.genericFiberPointDegree, if_pos hP]
  omega

/-- **General fibres.** Over an open subset of `T` containing the generic point, every closed
fibre of `g` is a prime divisor `E` in the smooth locus of `V` with `(E · E) = 0`. By adjunction
`(K · E) ≥ -2`, with equality only if `E ≅ ℙ¹_k`, and `(K · E) = -deg_{k(T)} B|_{V_η}` because
`(K + B) · E = 0`. -/
private theorem exists_open_smooth_fibre
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T]
    (hdimV : topologicalKrullDim V = 2) (hQ : IsQFactorial sV)
    (K : Divisor V) (hK : K.IsCanonicalDivisor sV 2) (B : QDivisor V)
    (g : V ⟶ T) [IsDominant g] {Δ : QDivisor V} (hg : IsMoriFibreSpace sV sT K Δ g)
    (hdimT : topologicalKrullDim T = 1)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sV g
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B))) :
    ∃ U : T.Opens, genericPoint T ∈ U ∧ ∀ w ∈ U, IsClosed ({w} : Set T) →
      ∃ (E : Mori.PrimeDivisor V) (C : ProperCurve sV), C.point = E.genericPoint ∧
        g E.genericPoint = w ∧ (E.support : Set V) = g.base ⁻¹' {w} ∧
        (E.support : Set V) ⊆ Mori.smoothLocus sV ∧
        -2 ≤ (Divisor.toQDivisor K).intersectionNumber k sV C.ι C.dim_le
          (isQCartier_of_isQFactorial sV hQ _) ∧
        ((Divisor.toQDivisor K).intersectionNumber k sV C.ι C.dim_le
            (isQCartier_of_isQFactorial sV hQ _) = -2 →
          ∃ e : projectiveLine k ≅ C.scheme, e.hom ≫ C.ι ≫ sV = projectiveLine k ↘ Spec (.of k)) ∧
        (Divisor.toQDivisor K).intersectionNumber k sV C.ι C.dim_le
          (isQCartier_of_isQFactorial sV hQ _) + MMP.Flips.genericFiberDegree g B = 0 := by
  classical
  obtain ⟨hVv, hVproj⟩ := (Mori.isProjectiveVariety_iff k sV).mp hg.isProjectiveVariety
  have : IsProper sV := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hVproj).2
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have : IsSeparated sV := hVv.toIsSeparated
  have hgc := hg.isContraction
  obtain ⟨hTv, hTn⟩ := hgc.isNormalVariety_target
  have : IsNormal T := hTn
  have : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  have : IsSeparated sT := hTv.toIsSeparated
  have : QuasiCompact sT := hTv.toQuasiCompact
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsProper g :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hgc.isProjectiveMorphism).2
  have : Surjective g := ⟨hgc.surjective⟩
  set Kq : QDivisor V := Divisor.toQDivisor K
  have hqc : ∀ D : QDivisor V, D.IsQCartier := isQCartier_of_isQFactorial sV hQ
  -- intersection numbers with a contracted curve are linear
  have hadd : ∀ (γ : ProperCurve sV) (D D' : QDivisor V),
      (D + D').intersectionNumber k sV γ.ι γ.dim_le (hqc _) =
        D.intersectionNumber k sV γ.ι γ.dim_le (hqc _) +
          D'.intersectionNumber k sV γ.ι γ.dim_le (hqc _) := fun γ D D' =>
    QDivisor.intersectionNumber_add' k sV γ.ι γ.dim_le D D' (hqc _) (hqc _) (hqc _)
  have hsmul : ∀ (γ : ProperCurve sV) (q : ℚ) (D : QDivisor V),
      (q • D).intersectionNumber k sV γ.ι γ.dim_le (hqc _) =
        q * D.intersectionNumber k sV γ.ι γ.dim_le (hqc _) := fun γ q D =>
    intersectionNumber_smul sV γ.ι γ.dim_le D (hqc _) q (hqc _)
  have hKB0 : ∀ γ : ProperCurve sV, γ.IsContractedBy g →
      (Kq + B).intersectionNumber k sV γ.ι γ.dim_le (hqc _) = 0 :=
    intersectionNumber_eq_zero_of_isNumericallyTrivialOver sV hQ hnum
  -- the singular points of `V` and their images
  set S₀ : Set V := ((Mori.smoothLocus sV : V.Opens) : Set V)ᶜ
  have hS₀cl : ∀ z ∈ S₀, IsClosed ({z} : Set V) := fun z hz =>
    isClosed_singleton_of_notMem_smoothLocus sV hVv hdimV hz
  have : IsNoetherian V := {}
  have hS₀ : S₀.Finite := finite_of_isClosed_of_forall_isClosed
    (Mori.smoothLocus sV).isOpen.isClosed_compl hS₀cl
  have hgS : IsClosed (g.base '' S₀) := by
    rw [← Set.biUnion_of_singleton S₀, Set.image_iUnion₂]
    refine hS₀.isClosed_biUnion fun z hz => ?_
    rw [Set.image_singleton]
    have := g.isClosedMap _ (hS₀cl z hz)
    rwa [Set.image_singleton] at this
  have hηgS : genericPoint T ∉ g.base '' S₀ := by
    rintro ⟨z, hz, hzη⟩
    have := g.isClosedMap _ (hS₀cl z hz)
    rw [Set.image_singleton, hzη] at this
    exact not_isClosed_genericPoint hdimT this
  obtain ⟨U, hU, hUw⟩ := exists_dense_open_genericFiberDegree_eq sV sT hdimV hQ g hg hdimT B
  have hηU : genericPoint T ∈ U :=
    ((genericPoint_spec T).mem_open_set_iff U.isOpen).mpr
      (by rw [Set.univ_inter]; exact hU.nonempty)
  have hfib : ∀ w ∈ (U : Set T) ∩ (g.base '' S₀)ᶜ, IsClosed ({w} : Set T) →
      ∃ (E : Mori.PrimeDivisor V) (C : ProperCurve sV), C.point = E.genericPoint ∧
        g E.genericPoint = w ∧ (E.support : Set V) = g.base ⁻¹' {w} ∧
        (E.support : Set V) ⊆ Mori.smoothLocus sV ∧
        -2 ≤ Kq.intersectionNumber k sV C.ι C.dim_le (hqc _) ∧
        (Kq.intersectionNumber k sV C.ι C.dim_le (hqc _) = -2 →
          ∃ e : projectiveLine k ≅ C.scheme, e.hom ≫ C.ι ≫ sV = projectiveLine k ↘ Spec (.of k)) ∧
        Kq.intersectionNumber k sV C.ι C.dim_le (hqc _) + MMP.Flips.genericFiberDegree g B = 0 := by
    rintro w ⟨hwU, hwS⟩ hwc
    obtain ⟨C, hCc, hCw, hcl, hgd⟩ := hUw w hwU hwc
    have hfibsm : g.base ⁻¹' {w} ⊆ (Mori.smoothLocus sV : Set V) := fun x hx => by
      by_contra h
      exact hwS ⟨x, h, hx⟩
    -- the fibre over `w` is a prime divisor `E` with `(E · E) = 0`
    obtain ⟨Pw, hPw, hBw, Fw, hFw⟩ := exists_isPullback_fibre g hgc.surjective hdimT w hwc
    have hCmem : C.point ∈ Fw.supp :=
      mem_supp_of_isPullback_single g Pw hFw (x := C.point) (hCw.trans hPw.symm)
    obtain ⟨E, hE, hCE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hCmem
    have hEw : g E.genericPoint = w := by
      by_contra h
      exact hE (coeff_eq_zero_of_isPullback_single g Pw (hPw ▸ hwc) hFw E (hPw ▸ h))
    have hEfib : E.support ⊆ g.base ⁻¹' {w} := by
      intro x hx
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
      have h1 := (specializes_iff_mem_closure.mpr hx).map g.continuous
      rw [hEw] at h1
      have := specializes_iff_mem_closure.mp h1
      rwa [hwc.closure_eq] at this
    have hCE' : C.point = E.genericPoint := by
      have h1 : E.genericPoint ⤳ C.point := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hCE
        exact specializes_iff_mem_closure.mpr hCE
      have h2 : C.point ⤳ E.genericPoint := by
        have : E.genericPoint ∈ closure ({C.point} : Set V) := by
          rw [hcl]
          refine hEfib ?_
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact subset_closure rfl
        exact specializes_iff_mem_closure.mpr this
      exact (inseparable_iff_specializes_and.mpr ⟨h2, h1⟩).eq
    have hEsupp : (E.support : Set V) = g.base ⁻¹' {w} := by
      refine le_antisymm hEfib fun x hx => ?_
      have : x ∈ closure ({C.point} : Set V) := by rw [hcl]; exact hx
      rwa [hCE', ← AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
    have hFwE : ∀ E', E' ≠ E → Fw E' = 0 := by
      intro E' hE'
      by_contra h
      have hE'w : g E'.genericPoint = w := by
        by_contra h'
        exact h (coeff_eq_zero_of_isPullback_single g Pw (hPw ▸ hwc) hFw E' (hPw ▸ h'))
      have : E'.genericPoint ∈ E.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        change E'.genericPoint ∈ closure ({E.genericPoint} : Set V)
        rw [← hCE', hcl]
        exact hE'w
      exact hE' (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E E' this).symm
    have hFwq : Divisor.toQDivisor Fw = ((Fw E : ℤ) : ℚ) • Divisor.toQDivisor (Finsupp.single E 1) := by
      ext E'
      change DivisorWithCoeffs.coeff (Divisor.toQDivisor Fw) E' =
        (Fw E : ℚ) * DivisorWithCoeffs.coeff (Divisor.toQDivisor (Finsupp.single E 1)) E'
      rw [Divisor.coeff_toQDivisor, Divisor.coeff_toQDivisor]
      by_cases h : E' = E
      · subst h; rw [DivisorWithCoeffs.coeff_single_self]; simp; rfl
      · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm h)]
        have : DivisorWithCoeffs.coeff Fw E' = 0 := hFwE E' h
        rw [this]; simp
    have hFw0 := intersectionNumber_eq_zero_of_isPullback_single g sV hQ Pw hFw (hqc _) C
      fun x hx => by
        have : x ∈ closure ({C.point} : Set V) := specializes_iff_mem_closure.mp hx
        rw [hcl] at this
        exact this.trans hPw.symm
    have hFwpos : (0 : ℚ) < Fw E := by
      exact_mod_cast coeff_pos_of_isPullback_single g Pw hFw E (hEw.trans hPw.symm)
    have hEE : (Divisor.toQDivisor (Finsupp.single E 1)).intersectionNumber k sV C.ι C.dim_le
        (hqc _) = 0 := by
      rw [intersectionNumber_congr sV C.ι C.dim_le (hqc _) (hqc _) hFwq, hsmul] at hFw0
      rcases mul_eq_zero.mp hFw0 with h | h
      · exact absurd h hFwpos.ne'
      · exact h
    have hEsm : E.support ⊆ (Mori.smoothLocus sV : Set V) := hEfib.trans hfibsm
    obtain ⟨hK2, hiso⟩ := neg_two_le_intersectionNumber_canonical sV hVv hQ K hK E hEsm C
      hCE' hEE
    have hKB := hKB0 C hCc
    rw [hadd, ← hgd] at hKB
    exact ⟨E, C, hCE', hEw, hEsupp, hEsm, hK2, hiso, hKB⟩
  exact ⟨⟨_, U.isOpen.inter hgS.isOpen_compl⟩, ⟨hηU, hηgS⟩, hfib⟩

/-- **The horizontal floor.** It is a section, a bisection, or two sections. -/
private theorem horizontalFloor_cases
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T]
    (hdimV : topologicalKrullDim V = 2) (hQ : IsQFactorial sV)
    (K : Divisor V) (hK : K.IsCanonicalDivisor sV 2)
    (B : QDivisor V) (hlc : MMP.Intersection.IsLogCanonicalPair sV B)
    (ε : ℚ) (hε : 0 < ε ∧ ε < 1)
    (g : V ⟶ T) [IsDominant g]
    (hg : IsMoriFibreSpace sV sT K (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)) g)
    (hdimT : topologicalKrullDim T = 1)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sV g
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B))) :
    let H : Set (Mori.PrimeDivisor V) :=
      {P | ⌊B.coeff P⌋ ≠ 0 ∧ g.base P.genericPoint = genericPoint T}
    let deg : Mori.PrimeDivisor V → ℕ := fun P =>
      letI := (g.residueFieldMap P.genericPoint).hom.toAlgebra
      Module.finrank (T.residueField (g.base P.genericPoint)) (V.residueField P.genericPoint)
    (∃ P, H = {P} ∧ deg P = 1) ∨ (∃ P, H = {P} ∧ deg P = 2) ∨
      (∃ P₁ P₂, P₁ ≠ P₂ ∧ H = {P₁, P₂} ∧ deg P₁ = 1 ∧ deg P₂ = 1) := by
  classical
  intro H deg
  obtain ⟨hVv, hVproj⟩ := (Mori.isProjectiveVariety_iff k sV).mp hg.isProjectiveVariety
  have : IsProper sV := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hVproj).2
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have : IsSeparated sV := hVv.toIsSeparated
  have hgc := hg.isContraction
  obtain ⟨hTv, hTn⟩ := hgc.isNormalVariety_target
  have : IsNormal T := hTn
  have : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  have : IsSeparated sT := hTv.toIsSeparated
  have : QuasiCompact sT := hTv.toQuasiCompact
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsProper g :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hgc.isProjectiveMorphism).2
  have : Surjective g := ⟨hgc.surjective⟩
  obtain ⟨m₀, hm₀, L₀, hL₀, hL₀eq, hL₀a⟩ := hg.hasRelativelyAmpleMultiple
  have hpos : ∀ γ : ProperCurve sV, γ.IsContractedBy g →
      0 < L₀.degreeOn k sV γ.ι γ.dim_le hL₀ := by
    intro γ hγ
    have := hL₀.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple hVv g L₀.divisorialSheaf
      hL₀a γ hγ
  have hB0 : ∀ E, 0 ≤ B E := hlc.2.1
  set Kq : QDivisor V := Divisor.toQDivisor K
  set F : QDivisor V := Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)
  have hqc : ∀ D : QDivisor V, D.IsQCartier := isQCartier_of_isQFactorial sV hQ
  -- intersection numbers with a contracted curve are linear
  have hadd : ∀ (γ : ProperCurve sV) (D D' : QDivisor V),
      (D + D').intersectionNumber k sV γ.ι γ.dim_le (hqc _) =
        D.intersectionNumber k sV γ.ι γ.dim_le (hqc _) +
          D'.intersectionNumber k sV γ.ι γ.dim_le (hqc _) := fun γ D D' =>
    QDivisor.intersectionNumber_add' k sV γ.ι γ.dim_le D D' (hqc _) (hqc _) (hqc _)
  have hsmul : ∀ (γ : ProperCurve sV) (q : ℚ) (D : QDivisor V),
      (q • D).intersectionNumber k sV γ.ι γ.dim_le (hqc _) =
        q * D.intersectionNumber k sV γ.ι γ.dim_le (hqc _) := fun γ q D =>
    intersectionNumber_smul sV γ.ι γ.dim_le D (hqc _) q (hqc _)
  have hKB0 : ∀ γ : ProperCurve sV, γ.IsContractedBy g →
      (Kq + B).intersectionNumber k sV γ.ι γ.dim_le (hqc _) = 0 :=
    intersectionNumber_eq_zero_of_isNumericallyTrivialOver sV hQ hnum
  have hFpos : ∀ γ : ProperCurve sV, γ.IsContractedBy g →
      0 < F.intersectionNumber k sV γ.ι γ.dim_le (hqc _) := by
    intro γ hγ
    have h1 : 0 < (-(Kq + (B - ε • F))).intersectionNumber k sV γ.ι γ.dim_le (hqc _) := by
      rw [QDivisor.intersectionNumber_eq_of_smul k sV γ.ι γ.dim_le _ _ hm₀ L₀ hL₀ hL₀eq]
      have := hpos γ hγ
      have : (0 : ℚ) < L₀.degreeOn k sV γ.ι γ.dim_le hL₀ := by exact_mod_cast this
      positivity
    have e1 : -(Kq + (B - ε • F)) = (-1 : ℚ) • (Kq + B) + ε • F := by
      rw [neg_one_smul]; abel
    rw [intersectionNumber_congr sV γ.ι γ.dim_le (hqc _) (hqc _) e1, hadd, hsmul, hsmul,
      hKB0 γ hγ] at h1
    have hε0 := hε.1
    nlinarith
  have hgfpd : ∀ P ∈ H, MMP.Flips.genericFiberPointDegree g P = deg P := fun P hP => by
    simp only [MMP.Flips.genericFiberPointDegree, deg]
    rw [if_pos hP.2]
  have hFcoeff : ∀ E, F E = (⌊B E⌋ : ℚ) := fun E => by
    change DivisorWithCoeffs.coeff (Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)) E = _
    rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_roundDown]
    rfl
  have hBH : ∀ P ∈ H, 1 ≤ B P := fun P hP => by
    have h1 : ⌊B P⌋ ≠ 0 := hP.1
    have h2 : 0 ≤ ⌊B P⌋ := Int.floor_nonneg.mpr (hB0 P)
    have h3 : 1 ≤ ⌊B P⌋ := by omega
    exact Int.le_floor.mp (by exact_mod_cast h3)
  -- (i) the horizontal floor is nonempty
  have hHne : H.Nonempty := by
    obtain ⟨U, hU, hUw⟩ := exists_dense_open_genericFiberDegree_eq sV sT hdimV hQ g hg hdimT F
    obtain ⟨w, hwU, hwc⟩ := exists_isClosed_mem_of_isOpen sT U.isOpen hU.nonempty
    obtain ⟨C, hCc, -, -, hgd⟩ := hUw w hwU hwc
    have h1 := hFpos C hCc
    rw [← hgd] at h1
    unfold MMP.Flips.genericFiberDegree at h1
    obtain ⟨E, -, hE0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1.ne'
    refine ⟨E, ?_, ?_⟩
    · intro h
      apply hE0
      have : F.coeff E = 0 := by
        change F E = 0
        rw [hFcoeff]
        have : ⌊B E⌋ = 0 := h
        rw [this]; simp
      rw [this, zero_mul]
    · by_contra h
      apply hE0
      simp [MMP.Flips.genericFiberPointDegree, h]
  -- (ii) every horizontal floor component has positive generic degree
  have hdeg_pos : ∀ P ∈ H, 1 ≤ deg P := fun P hP => by
    have := one_le_genericFiberPointDegree sV sT hdimV hQ g hg hdimT P hP.2
    rwa [hgfpd P hP] at this
  -- (iii) the total floor degree is at most two
  obtain ⟨U, hηU, hfib⟩ := exists_open_smooth_fibre sV sT hdimV hQ K hK B g hg hdimT hnum
  obtain ⟨w, hwU, hwc⟩ := exists_isClosed_mem_of_isOpen sT U.isOpen ⟨_, hηU⟩
  obtain ⟨-, C, -, -, -, -, hK2, -, hKB⟩ := hfib w hwU hwc
  have hBdeg : MMP.Flips.genericFiberDegree g B ≤ 2 := by linarith
  -- comparison with the generic fibre degree
  set Hs : Finset (Mori.PrimeDivisor V) := B.support.filter (· ∈ H)
  have hHs : (Hs : Set (Mori.PrimeDivisor V)) = H := by
    ext P
    simp only [Hs, Finset.coe_filter, Set.mem_setOf_eq, Finsupp.mem_support_iff]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨fun h0 => ?_, h⟩
      have := hBH P h
      change B P = 0 at h0
      linarith
  have hsum : (∑ P ∈ Hs, (deg P : ℚ)) ≤ 2 := by
    refine le_trans ?_ hBdeg
    unfold MMP.Flips.genericFiberDegree
    calc (∑ P ∈ Hs, (deg P : ℚ)) ≤ ∑ P ∈ Hs, B.coeff P * MMP.Flips.genericFiberPointDegree g P := by
          refine Finset.sum_le_sum fun P hP => ?_
          have hPH : P ∈ H := (Finset.mem_filter.mp hP).2
          rw [hgfpd P hPH]
          have := hBH P hPH
          have h0 : (0 : ℚ) ≤ deg P := by positivity
          change (deg P : ℚ) ≤ B P * _
          nlinarith
      _ ≤ ∑ E ∈ B.support, B.coeff E * MMP.Flips.genericFiberPointDegree g E := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun E _ _ => ?_
          exact mul_nonneg (hB0 E) (by positivity)
  -- (iv) counting
  have hdeg1 : ∀ P ∈ Hs, (1 : ℚ) ≤ deg P := fun P hP => by
    exact_mod_cast hdeg_pos P (Finset.mem_filter.mp hP).2
  have hcard : (Hs.card : ℚ) ≤ 2 := by
    calc (Hs.card : ℚ) = ∑ P ∈ Hs, (1 : ℚ) := by simp
      _ ≤ ∑ P ∈ Hs, (deg P : ℚ) := Finset.sum_le_sum hdeg1
      _ ≤ 2 := hsum
  have hHsne : Hs.Nonempty := by
    obtain ⟨P, hP⟩ := hHne
    exact ⟨P, by rw [← Finset.mem_coe, hHs]; exact hP⟩
  have hc1 : 1 ≤ Hs.card := Finset.card_pos.mpr hHsne
  have hc2 : Hs.card ≤ 2 := by exact_mod_cast hcard
  rcases (show Hs.card = 1 ∨ Hs.card = 2 by omega) with h | h
  · obtain ⟨P, hP⟩ := Finset.card_eq_one.mp h
    have hHP : H = {P} := by rw [← hHs, hP]; simp
    have hdP : (deg P : ℚ) ≤ 2 := by simpa [hP] using hsum
    have hd1 : 1 ≤ deg P := hdeg_pos P (by rw [hHP]; rfl)
    have hd2 : deg P ≤ 2 := by exact_mod_cast hdP
    rcases (show deg P = 1 ∨ deg P = 2 by omega) with h1 | h2
    · exact Or.inl ⟨P, hHP, h1⟩
    · exact Or.inr (Or.inl ⟨P, hHP, h2⟩)
  · obtain ⟨P₁, P₂, hne, hP⟩ := Finset.card_eq_two.mp h
    have hHP : H = {P₁, P₂} := by rw [← hHs, hP]; simp
    have hs : (deg P₁ : ℚ) + deg P₂ ≤ 2 := by
      rwa [hP, Finset.sum_pair hne] at hsum
    have h1 := hdeg_pos P₁ (by rw [hHP]; exact Or.inl rfl)
    have h2 := hdeg_pos P₂ (by rw [hHP]; exact Or.inr rfl)
    have hs' : deg P₁ + deg P₂ ≤ 2 := by exact_mod_cast hs
    exact Or.inr (Or.inr ⟨P₁, P₂, hne, hHP, by omega, by omega⟩)

/-- Two classes of `N₁(X)` with the same degree against every invertible sheaf are equal. -/
private theorem numericalCurveClasses_ext {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {u v : NumericalCurveClasses sX}
    (h : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      NumericalCurveClasses.degree sX L u = NumericalCurveClasses.degree sX L v) : u = v := by
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX u
  obtain ⟨Z', rfl⟩ := OneCycle.numericalClass_surjective sX v
  rw [OneCycle.numericalClass_eq_iff, OneCycle.numericallyEquivalent_iff_sub_mem,
    OneCycle.mem_numericallyTrivial]
  intro L _
  have := h L
  rw [NumericalCurveClasses.degree_numericalClass,
    NumericalCurveClasses.degree_numericalClass] at this
  rw [map_sub, this, sub_self]

/-- The intersection form of a numerical class on the class of a Cartier divisor `E` is the
degree of `𝒪_X(E)`. -/
private theorem numericalPairing_ofCartier {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (E : X.CartierDivisor) (u : NumericalCurveClasses sX) :
    numericalPairing sX (numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ E)) u =
      NumericalCurveClasses.degree sX (MMP.CartierDivisor.sheaf E) u := by
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX u
  rw [numericalPairing_apply, OneCycle.intersectionNumber_ofCartier,
    NumericalCurveClasses.degree_numericalClass]
  rfl

/-- The degree of a numerical class depends on the invertible sheaf only up to isomorphism. -/
private theorem NumericalCurveClasses.degree_eq_of_iso {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {L L' : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'] (e : L ≅ L')
    (u : NumericalCurveClasses sX) :
    NumericalCurveClasses.degree sX L u = NumericalCurveClasses.degree sX L' u := by
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX u
  rw [NumericalCurveClasses.degree_numericalClass, NumericalCurveClasses.degree_numericalClass,
    OneCycle.degree_apply, OneCycle.degree_apply]
  refine Finsupp.sum_congr fun C _ => ?_
  congr 2
  exact degreeOn_eq_of_iso k sX C.ι C.dim_le e

/-- **Classes orthogonal to the base.** If `ρ(X/Z) = 1`, a numerical class `u` of degree zero
against every pull-back from `Z` is a multiple `c [C₀]` of the class of a contracted curve `C₀`
on which an invertible sheaf `A` has positive degree; then `deg_u A = c deg_{C₀} A`. -/
private theorem eq_smul_of_degree_pullback_eq_zero {k : Type} [Field k] {X Z : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [IsIntegral X] [IsSeparated sZ]
    [LocallyOfFiniteType sZ]
    (f : X ⟶ Z) (hf : f ≫ sZ = sX) (hρ : relativePicardNumberN1 sX f = 1)
    (C₀ : ProperCurve sX) (hC₀ : C₀.IsContractedBy f)
    (A : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    (hA : 0 < C₀.degree k A) (u : NumericalCurveClasses sX)
    (hu : ∀ (M : Z.Modules) [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M],
      NumericalCurveClasses.degree sX ((Scheme.Modules.pullback f).obj M) u = 0) :
    u = (NumericalCurveClasses.degree sX A u / C₀.degree k A) •
      OneCycle.numericalClass sX (C₀.cycle ℝ) := by
  set ψ : NumericalDivisorClasses sX →ₗ[ℝ] ℝ := (numericalPairing sX).flip u
  have hψ : pullbackNumericalClasses sX f ≤ LinearMap.ker ψ := by
    rw [pullbackNumericalClasses, Submodule.span_le]
    rintro d ⟨E, M, hM, ⟨e⟩, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ψ, LinearMap.flip_apply]
    rw [numericalPairing_ofCartier, NumericalCurveClasses.degree_eq_of_iso e]
    exact hu M
  have hψ₀ := pullbackNumericalClasses_le_ker sX sZ f hf C₀ hC₀
  obtain ⟨EA, ⟨eA⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf A
  set a := numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ EA)
  have hdegA : ∀ v : NumericalCurveClasses sX, numericalPairing sX a v =
      NumericalCurveClasses.degree sX A v := fun v => by
    rw [numericalPairing_ofCartier, NumericalCurveClasses.degree_eq_of_iso eA.symm]
  have hC₀A : NumericalCurveClasses.degree sX A (OneCycle.numericalClass sX (C₀.cycle ℝ)) =
      C₀.degree k A := by
    rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
  have hA' : (0 : ℝ) < C₀.degree k A := by exact_mod_cast hA
  refine numericalCurveClasses_ext fun L _ => ?_
  obtain ⟨EL, ⟨eL⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf L
  set b := numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ EL)
  have key := mul_comm_of_toENat_rank_eq_one hρ
    ((pullbackNumericalClasses sX f).liftQ ψ hψ) ((pullbackNumericalClasses sX f).liftQ _ hψ₀)
    ((pullbackNumericalClasses sX f).mkQ b) ((pullbackNumericalClasses sX f).mkQ a)
  simp only [Submodule.liftQ_apply, Submodule.mkQ_apply, ψ, LinearMap.flip_apply] at key
  rw [hdegA, hdegA, hC₀A] at key
  have hbL : ∀ v : NumericalCurveClasses sX, numericalPairing sX b v =
      NumericalCurveClasses.degree sX L v := fun v => by
    rw [numericalPairing_ofCartier, NumericalCurveClasses.degree_eq_of_iso eL.symm]
  rw [hbL, hbL] at key
  rw [map_smul, smul_eq_mul]
  field_simp
  linarith

/-- An invertible sheaf of nonnegative degree on every curve has nonnegative degree on `NE̅(X)`. -/
private theorem degree_nonneg_of_mem_closedConeOfCurves {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : ∀ γ : ProperCurve sX, 0 ≤ γ.degree k L) {u : NumericalCurveClasses sX}
    (hu : u ∈ closedConeOfCurves sX) : 0 ≤ NumericalCurveClasses.degree sX L u := by
  have hcl : IsClosed {v : NumericalCurveClasses sX | 0 ≤ NumericalCurveClasses.degree sX L v} :=
    isClosed_le continuous_const (NumericalCurveClasses.continuous_degree sX L)
  have hsub : (coneOfCurves sX : Set (NumericalCurveClasses sX)) ⊆
      {v | 0 ≤ NumericalCurveClasses.degree sX L v} := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨γ, rfl⟩ := hx
      show 0 ≤ NumericalCurveClasses.degree sX L (OneCycle.numericalClass sX (γ.cycle ℝ))
      rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
      exact_mod_cast hL γ
    | zero => simp
    | add x y _ _ hx hy =>
      show 0 ≤ NumericalCurveClasses.degree sX L (x + y)
      rw [map_add]; exact add_nonneg hx hy
    | smul c x _ hx =>
      show 0 ≤ NumericalCurveClasses.degree sX L (c • x)
      rw [show c • x = (c : ℝ) • x from rfl, map_smul, smul_eq_mul]
      exact mul_nonneg c.2 hx
  have := closure_minimal hsub hcl
  rw [← coe_closedConeOfCurves] at this
  exact this hu

/-- An ample invertible sheaf has positive degree on every proper curve. -/
private theorem degree_pos_of_isAmple' {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (D : ProperCurve sX) (H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H]
    (hH : Scheme.Modules.IsAmple X H) : 0 < D.degree k H := by
  have := D.isCurve
  exact invertibleCurveDegree_pos_of_isAmple_of_isCurve k (D.ι ≫ sX) D.dim_le _
    (isAmple_pullback_of_isFinite D.ι H hH)

/-- On a proper integral curve, the generic point is the only proper curve. -/
private theorem isProperCurve_iff_eq_genericPoint {k : Type} [Field k] {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of k)) [IsIntegral T] [IsProper sT] [LocallyOfFiniteType sT]
    [CompactSpace T] (hdimT : topologicalKrullDim T = 1) (y : T) :
    IsProperCurve sT y ↔ y = genericPoint T := by
  constructor
  · intro h
    by_contra hy
    exact not_isClosed_singleton_point (⟨y, h⟩ : ProperCurve sT)
      (isClosed_singleton_of_ne_genericPoint sT hdimT hy)
  · rintro rfl
    refine isProperCurve_of_isProper sT ?_
    rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, (genericPoint_spec T).def,
      (Homeomorph.Set.univ T).isHomeomorph.topologicalKrullDim_eq, hdimT]

/-- **Pull-backs from a curve are numerically proportional.** On `f : X ⟶ T` onto a proper
integral curve, the degree forms of `f^* M` and `f^* H` on `N₁(X)` are proportional, with factor
`deg_T M / deg_T H`. -/
private theorem degree_pullback_eq_mul {k : Type} [Field k] {X T : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (sT : T ⟶ Spec (.of k)) [IsIntegral T] [IsProper sT]
    [IsSeparated sT] [LocallyOfFiniteType sT] [CompactSpace T]
    (hdimT : topologicalKrullDim T = 1) (f : X ⟶ T) (hf : f ≫ sT = sX)
    (M H : T.Modules) [SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 H]
    (ΓT : ProperCurve sT) (u : NumericalCurveClasses sX) :
    (ΓT.degree k H : ℝ) * NumericalCurveClasses.degree sX ((Scheme.Modules.pullback f).obj M) u =
      (ΓT.degree k M : ℝ) * NumericalCurveClasses.degree sX ((Scheme.Modules.pullback f).obj H) u := by
  have hcurve : ∀ γ : ProperCurve sX,
      (ΓT.degree k H : ℝ) * (γ.degree k ((Scheme.Modules.pullback f).obj M) : ℝ) =
        (ΓT.degree k M : ℝ) * (γ.degree k ((Scheme.Modules.pullback f).obj H) : ℝ) := by
    intro γ
    rw [γ.degree_pullback f hf M, γ.degree_pullback f hf H]
    split_ifs with h
    · have hΓ : (⟨f γ.point, h⟩ : ProperCurve sT) = ΓT := by
        ext
        exact ((isProperCurve_iff_eq_genericPoint sT hdimT _).mp h).trans
          ((isProperCurve_iff_eq_genericPoint sT hdimT _).mp ΓT.isProperCurve).symm
      rw [hΓ]; push_cast; ring
    · simp
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX u
  rw [NumericalCurveClasses.degree_numericalClass, NumericalCurveClasses.degree_numericalClass,
    OneCycle.degree_apply, OneCycle.degree_apply, Finsupp.mul_sum, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun γ _ => ?_
  have := hcurve γ
  calc (ΓT.degree k H : ℝ) * (Z γ * (γ.degree k ((Scheme.Modules.pullback f).obj M) : ℝ))
      = Z γ * ((ΓT.degree k H : ℝ) * (γ.degree k ((Scheme.Modules.pullback f).obj M) : ℝ)) := by
        ring
    _ = Z γ * ((ΓT.degree k M : ℝ) * (γ.degree k ((Scheme.Modules.pullback f).obj H) : ℝ)) := by
        rw [this]
    _ = _ := by ring

/-- **A rank-one fibration onto a curve is the contraction of an extremal ray.** Let
`g : V ⟶ T` be a contraction of a projective variety onto a projective curve with
`ρ(V/T) = 1`, and `D` a `ℚ`-Cartier divisor negative on every contracted curve. The classes
`c [C₀]`, `c ≥ 0`, of a contracted curve `C₀` form a `D`-negative extremal ray of `NE̅(V)`, and `g`
is its contraction. -/
private theorem exists_isContractionOfRay {k : Type} [Field k] {V T : Scheme.{0}}
    (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T] [IsProper sT] [IsSeparated sT] [LocallyOfFiniteType sT] [CompactSpace T]
    (hVp : Mori.IsProjectiveVariety k sV) (hTp : Mori.IsProjectiveVariety k sT)
    (hdimT : topologicalKrullDim T = 1) (g : V ⟶ T) (hgc : IsContraction sV sT g)
    (hρ : relativePicardNumberN1 sV g = 1) (D : QDivisor V) (hD : D.IsQCartier)
    (hneg : ∀ γ : ProperCurve sV, γ.IsContractedBy g →
      QDivisor.curveForm sV D hD (OneCycle.numericalClass sV (γ.cycle ℝ)) < 0)
    (C₀ : ProperCurve sV) (hC₀ : C₀.IsContractedBy g) :
    ∃ R, IsNegativeExtremalRayOf sV D R ∧ IsContractionOfRay sV sT R g := by
  obtain ⟨HV, hHVi, hHVa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hVp
  obtain ⟨HT, hHTi, hHTa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hTp
  have hgs := hgc.comp_eq
  have hη := (isProperCurve_iff_eq_genericPoint sT hdimT (genericPoint T)).mpr rfl
  set ΓT : ProperCurve sT := ⟨genericPoint T, hη⟩
  have hΓH : 0 < ΓT.degree k HT := degree_pos_of_isAmple' ΓT HT hHTa
  set ℓ := NumericalCurveClasses.degree sV ((Scheme.Modules.pullback g).obj HT)
  have hℓcls : ∀ γ : ProperCurve sV, ℓ (OneCycle.numericalClass sV (γ.cycle ℝ)) =
      (γ.degree k ((Scheme.Modules.pullback g).obj HT) : ℝ) := fun γ => by
    rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
  have hℓcurve : ∀ γ : ProperCurve sV, 0 ≤ γ.degree k ((Scheme.Modules.pullback g).obj HT) := by
    intro γ
    rw [γ.degree_pullback g hgs HT]
    split_ifs with h
    · have hΓ : (⟨g γ.point, h⟩ : ProperCurve sT) = ΓT :=
        ProperCurve.ext ((isProperCurve_iff_eq_genericPoint sT hdimT _).mp h)
      rw [hΓ]; exact mul_nonneg (by positivity) hΓH.le
    · exact le_rfl
  have hHVcurve : ∀ γ : ProperCurve sV, 0 ≤ γ.degree k HV := fun γ =>
    (degree_pos_of_isAmple' γ HV hHVa).le
  have hC₀HV := degree_pos_of_isAmple' C₀ HV hHVa
  have hC₀HV' : (0 : ℝ) < C₀.degree k HV := by exact_mod_cast hC₀HV
  have hker : ∀ u, ℓ u = 0 → u = (NumericalCurveClasses.degree sV HV u / C₀.degree k HV) •
      OneCycle.numericalClass sV (C₀.cycle ℝ) := by
    intro u hu
    refine eq_smul_of_degree_pullback_eq_zero sV sT g hgs hρ C₀ hC₀ HV hC₀HV u fun M _ => ?_
    have h1 := degree_pullback_eq_mul sT hdimT g hgs M HT ΓT u
    change _ = _ * ℓ u at h1
    rw [hu, mul_zero] at h1
    have hΓH' : (ΓT.degree k HT : ℝ) ≠ 0 := by exact_mod_cast hΓH.ne'
    exact (mul_eq_zero.mp h1).resolve_left hΓH'
  set R : Set (NumericalCurveClasses sV) :=
    {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sV (C₀.cycle ℝ) = w}
  have hℓC₀ : ℓ (OneCycle.numericalClass sV (C₀.cycle ℝ)) = 0 := by
    rw [hℓcls, C₀.degree_pullback_eq_zero_of_isContractedBy g hgs hC₀ HT, Int.cast_zero]
  have hmemR : ∀ u ∈ closedConeOfCurves sV, ℓ u = 0 → u ∈ R := fun u hu h0 =>
    ⟨_, div_nonneg (degree_nonneg_of_mem_closedConeOfCurves HV hHVcurve hu) hC₀HV'.le,
      (hker u h0).symm⟩
  have hC₀mem : OneCycle.numericalClass sV (C₀.cycle ℝ) ∈ closedConeOfCurves sV :=
    coneOfCurves_le_closedConeOfCurves sV (PointedCone.subset_hull ⟨C₀, rfl⟩)
  have hRcone : R ⊆ closedConeOfCurves sV := by
    rintro _ ⟨c, hc, rfl⟩
    exact (closedConeOfCurves sV).smul_mem hc hC₀mem
  have hC₀ne : OneCycle.numericalClass sV (C₀.cycle ℝ) ≠ 0 := fun h => by
    have := NumericalCurveClasses.degree_numericalClass sV HV (C₀.cycle ℝ)
    rw [h, map_zero, OneCycle.degree_cycle] at this
    exact hC₀HV'.ne this
  have hR : IsExtremalRay ℝ (closedConeOfCurves sV : Set (NumericalCurveClasses sV)) R := by
    refine ⟨⟨hRcone, ⟨⟨0, le_rfl, zero_smul _ _⟩, ?_⟩, ?_, ?_⟩, _, hC₀ne, rfl⟩
    · rintro _ ⟨c, hc, rfl⟩ d hd
      exact ⟨d * c, mul_nonneg hd.le hc, by rw [mul_smul]⟩
    · rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
      exact ⟨c + d, add_nonneg hc hd, by rw [add_smul]⟩
    · intro u hu v hv huv
      obtain ⟨c, -, hc⟩ := huv
      have h0 : ℓ u + ℓ v = 0 := by rw [← map_add, ← hc, map_smul, hℓC₀, smul_zero]
      have hu0 := degree_nonneg_of_mem_closedConeOfCurves _ hℓcurve hu
      have hv0 := degree_nonneg_of_mem_closedConeOfCurves _ hℓcurve hv
      exact ⟨hmemR u hu (by linarith), hmemR v hv (by linarith)⟩
  refine ⟨R, ⟨hD, hR, ?_⟩, ⟨hgc, fun γ => ?_⟩⟩
  · rintro _ ⟨c, hc, rfl⟩ hne
    have hc' : 0 < c := lt_of_le_of_ne hc fun h => hne (by rw [← h, zero_smul])
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hc' (hneg C₀ hC₀)
  · constructor
    · intro hγ
      refine hmemR _ (coneOfCurves_le_closedConeOfCurves sV (PointedCone.subset_hull ⟨γ, rfl⟩)) ?_
      rw [hℓcls, γ.degree_pullback_eq_zero_of_isContractedBy g hgs hγ HT, Int.cast_zero]
    · rintro ⟨c, -, hc⟩
      refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero g hgs HT hHTa γ ?_
      have : ℓ (OneCycle.numericalClass sV (γ.cycle ℝ)) = 0 := by
        rw [← hc, map_smul, hℓC₀, smul_zero]
      rw [hℓcls] at this
      exact_mod_cast this

/-- **Rational pluriforms with a prescribed divisor.** On a normal variety over a perfect field
with canonical divisor `K`, if `mK - C` is principal then some rational `m`-canonical form has
divisor `C`. -/
private theorem exists_ordForm_eq_of_principal {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) (m : ℕ)
    (C : Divisor X) (φ : (RationalFunctions X)ˣ)
    (hC : ∀ Γ : Mori.PrimeDivisor X, (m : ℤ) * K.coeff Γ - C.coeff Γ = Γ.ord φ) :
    ∃ τ : RationalPluriForms sX n m, τ ≠ 0 ∧ ∀ Γ : Mori.PrimeDivisor X,
      Γ.ordForm τ = C.coeff Γ := by
  have hn := hK.topologicalKrullDim_eq
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hX hn
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨g, hg0, hg⟩ := MMP.Positivity.exists_ord_eq_of_units φ
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  have hcg : c ^ (m : ℤ) * g⁻¹ ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (inv_ne_zero hg0)
  let τ : RationalPluriForms sX n m := (c ^ (m : ℤ) * g⁻¹) • ZTensorPower.basis b m ()
  have hrepr : (ZTensorPower.basis b m).repr τ () = c ^ (m : ℤ) * g⁻¹ := by
    simp [τ]
  have hτ : τ ≠ 0 := smul_ne_zero hcg ((ZTensorPower.basis b m).ne_zero ())
  refine ⟨τ, hτ, fun Γ => ?_⟩
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 ω hω0
  have e2 := hN m τ hτ
  rw [hrepr, Scheme.ord_mul (zpow_ne_zero _ hc) (inv_ne_zero hg0), ord_zpow _ hc,
    ← zpow_neg_one, ord_zpow _ hg0] at e2
  rw [← hc_def, hω Γ] at e1
  have hgΓ := (hC Γ).trans (hg Γ)
  linear_combination e2 - (m : ℤ) * e1 + hgΓ

/-- **Relatively trivial divisors descend.** On the Mori fibre space, a `ℚ`-divisor of degree
zero on every contracted curve is `ℚ`-linearly equivalent to a pull-back from `T`. -/
private theorem exists_qLinearlyEquivalent_pullback
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T]
    (hdimV : topologicalKrullDim V = 2) (hQ : IsQFactorial sV)
    (K : Divisor V) (hK : K.IsCanonicalDivisor sV 2)
    (B : QDivisor V) (ε : ℚ)
    (hklt : IsKltPair sV (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))
    (g : V ⟶ T) [IsDominant g]
    (hg : IsMoriFibreSpace sV sT K (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)) g)
    (hdimT : topologicalKrullDim T = 1)
    [IsLocallyNoetherian T] [IsNormal T] (L : QDivisor V)
    (hL : ∀ γ : ProperCurve sV, γ.IsContractedBy g →
      L.intersectionNumber k sV γ.ι γ.dim_le (isQCartier_of_isQFactorial sV hQ L) = 0) :
    ∃ (M : QDivisor T) (hM : M.IsQCartier)
      (hMf : ∀ Z : irreducibleComponents V, g (componentGenericPoint V Z) ∉ M.supp),
      L.QLinearlyEquivalent (M.pullback hM hMf) := by
  classical
  obtain ⟨hVv, hVproj⟩ := (Mori.isProjectiveVariety_iff k sV).mp hg.isProjectiveVariety
  have : IsProper sV := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hVproj).2
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have hgc := hg.isContraction
  obtain ⟨hTv, hTn⟩ := hgc.isNormalVariety_target
  have : IsNormal T := hTn
  have : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  have : IsSeparated sT := hTv.toIsSeparated
  have : QuasiCompact sT := hTv.toQuasiCompact
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have hTproj := ((Mori.isProjectiveVariety_iff k sT).mp hg.isProjectiveVariety_target).2
  have : IsProper sT := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hTproj).2
  have : IsProper g :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hgc.isProjectiveMorphism).2
  obtain ⟨m₀, hm₀, L₀, hL₀, hL₀eq, hL₀a⟩ := hg.hasRelativelyAmpleMultiple
  have hpos : ∀ γ : ProperCurve sV, γ.IsContractedBy g →
      0 < L₀.degreeOn k sV γ.ι γ.dim_le hL₀ := by
    intro γ hγ
    have := hL₀.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple hVv g L₀.divisorialSheaf
      hL₀a γ hγ
  have hqc : ∀ D : QDivisor V, D.IsQCartier := isQCartier_of_isQFactorial sV hQ
  set D : QDivisor V := Divisor.toQDivisor K +
    (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B))
  have hneg : ∀ γ : ProperCurve sV, γ.IsContractedBy g →
      QDivisor.curveForm sV D (hqc D) (OneCycle.numericalClass sV (γ.cycle ℝ)) < 0 := by
    intro γ hγ
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
    have h1 : 0 < (-D).intersectionNumber k sV γ.ι γ.dim_le (hqc _) := by
      rw [QDivisor.intersectionNumber_eq_of_smul k sV γ.ι γ.dim_le _ _ hm₀ L₀ hL₀ hL₀eq]
      have : (0 : ℚ) < L₀.degreeOn k sV γ.ι γ.dim_le hL₀ := by exact_mod_cast hpos γ hγ
      positivity
    have h2 := intersectionNumber_smul sV γ.ι γ.dim_le D (hqc _) (-1) (hqc _)
    rw [intersectionNumber_congr sV γ.ι γ.dim_le (hqc _) (hqc _) (neg_one_smul ℚ D)] at h2
    rw [h2] at h1
    have : D.intersectionNumber k sV γ.ι γ.dim_le (hqc _) < 0 := by linarith
    exact_mod_cast this
  -- a contracted curve
  obtain ⟨t, -, ht⟩ := exists_isClosed_mem_of_isOpen sT isOpen_univ
    ⟨genericPoint T, Set.mem_univ _⟩
  obtain ⟨P, hPt, hB, F, hF⟩ := exists_isPullback_fibre g hgc.surjective hdimT t ht
  obtain ⟨x, hx⟩ := hgc.surjective t
  obtain ⟨E, hE, -⟩ := DivisorWithCoeffs.mem_supp_iff.mp
    (mem_supp_of_isPullback_single g P hF (x := x) (hx.trans hPt.symm))
  have hEt : g E.genericPoint = t := by
    by_contra h
    exact hE (coeff_eq_zero_of_isPullback_single g P (hPt ▸ ht) hF E (hPt ▸ h))
  set C₀ : ProperCurve sV := ⟨E.genericPoint, isProperCurve_genericPoint_of_dim_eq_two sV hdimV E⟩
  have hC₀ : C₀.IsContractedBy g := by
    intro y hy
    have h1 := (specializes_iff_mem_closure.mpr hy).map g.continuous
    change g E.genericPoint ⤳ g y at h1
    rw [hEt] at h1
    have := specializes_iff_mem_closure.mp h1
    rw [ht.closure_eq] at this
    change g y = g E.genericPoint
    rw [hEt]; exact this
  obtain ⟨R, hR, hf⟩ := exists_isContractionOfRay sV sT hg.isProjectiveVariety
    hg.isProjectiveVariety_target hdimT g hgc hg.relativePicardNumber_eq_one D (hqc D) hneg C₀ hC₀
  exact MMP.Fourfold.IsKltPair.exists_qLinearlyEquivalent_pullback_of_isContractionOfRay hklt
    hg.isProjectiveVariety ⟨2, hK⟩ hR hf hg.isProjectiveVariety_target
    ⟨hqc L, fun γ hγ => by
      rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
      exact_mod_cast hL γ hγ⟩

/-- **Two sections are relatively linearly equivalent.** If the horizontal floor consists of two
sections `P₁, P₂`, then `P₁ - P₂` is `ℚ`-linearly equivalent to a pull-back from `T`. -/
private theorem exists_qLinearlyEquivalent_sub_single
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T]
    (hdimV : topologicalKrullDim V = 2) (hQ : IsQFactorial sV)
    (K : Divisor V) (hK : K.IsCanonicalDivisor sV 2)
    (B : QDivisor V) (hlc : MMP.Intersection.IsLogCanonicalPair sV B)
    (ε : ℚ) (hε : 0 < ε ∧ ε < 1)
    (hklt : IsKltPair sV (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))
    (g : V ⟶ T) [IsDominant g]
    (hg : IsMoriFibreSpace sV sT K (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)) g)
    (hdimT : topologicalKrullDim T = 1)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sV g
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)))
    [IsLocallyNoetherian T] [IsNormal T] (P₁ P₂ : Mori.PrimeDivisor V)
    (hP₁ : g.base P₁.genericPoint = genericPoint T) (hP₂ : g.base P₂.genericPoint = genericPoint T)
    (hd₁ : (letI := (g.residueFieldMap P₁.genericPoint).hom.toAlgebra
      Module.finrank (T.residueField (g.base P₁.genericPoint)) (V.residueField P₁.genericPoint)) = 1)
    (hd₂ : (letI := (g.residueFieldMap P₂.genericPoint).hom.toAlgebra
      Module.finrank (T.residueField (g.base P₂.genericPoint)) (V.residueField P₂.genericPoint)) = 1) :
    ∃ (M : QDivisor T) (hM : M.IsQCartier)
      (hMf : ∀ Z : irreducibleComponents V, g (componentGenericPoint V Z) ∉ M.supp),
      (Divisor.toQDivisor (Finsupp.single P₁ 1) - Divisor.toQDivisor (Finsupp.single P₂ 1)).QLinearlyEquivalent
        (M.pullback hM hMf) := by
  classical
  obtain ⟨hVv, hVproj⟩ := (Mori.isProjectiveVariety_iff k sV).mp hg.isProjectiveVariety
  have : IsProper sV := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hVproj).2
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have : IsSeparated sV := hVv.toIsSeparated
  have hgc := hg.isContraction
  obtain ⟨hTv, hTn⟩ := hgc.isNormalVariety_target
  have : IsNormal T := hTn
  have : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  have : IsSeparated sT := hTv.toIsSeparated
  have : QuasiCompact sT := hTv.toQuasiCompact
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsProper g :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hgc.isProjectiveMorphism).2
  have : Surjective g := ⟨hgc.surjective⟩
  obtain ⟨m₀, hm₀, L₀, hL₀, hL₀eq, hL₀a⟩ := hg.hasRelativelyAmpleMultiple
  have hpos : ∀ γ : ProperCurve sV, γ.IsContractedBy g →
      0 < L₀.degreeOn k sV γ.ι γ.dim_le hL₀ := by
    intro γ hγ
    have := hL₀.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple hVv g L₀.divisorialSheaf
      hL₀a γ hγ
  have hqc : ∀ D : QDivisor V, D.IsQCartier := isQCartier_of_isQFactorial sV hQ
  set D₁ : QDivisor V := Divisor.toQDivisor (Finsupp.single P₁ 1)
  set D₂ : QDivisor V := Divisor.toQDivisor (Finsupp.single P₂ 1)
  obtain ⟨U₁, hU₁, h₁⟩ := exists_dense_open_genericFiberDegree_eq sV sT hdimV hQ g hg hdimT D₁
  obtain ⟨U₂, hU₂, h₂⟩ := exists_dense_open_genericFiberDegree_eq sV sT hdimV hQ g hg hdimT D₂
  have hη : genericPoint T ∈ (U₁ : Set T) ∩ U₂ :=
    ⟨((genericPoint_spec T).mem_open_set_iff U₁.isOpen).mpr
        (by rw [Set.univ_inter]; exact hU₁.nonempty),
      ((genericPoint_spec T).mem_open_set_iff U₂.isOpen).mpr
        (by rw [Set.univ_inter]; exact hU₂.nonempty)⟩
  obtain ⟨w, ⟨hw₁, hw₂⟩, hwc⟩ :=
    exists_isClosed_mem_of_isOpen sT (U₁.isOpen.inter U₂.isOpen) ⟨_, hη⟩
  obtain ⟨C, hCc, -, hcl, hgd₁⟩ := h₁ w hw₁ hwc
  obtain ⟨C', -, -, hcl', hgd₂⟩ := h₂ w hw₂ hwc
  have hCC' : C' = C := by
    refine ProperCurve.ext ?_
    have a1 : C.point ⤳ C'.point := specializes_iff_mem_closure.mpr
      (by rw [hcl, ← hcl']; exact subset_closure rfl)
    have a2 : C'.point ⤳ C.point := specializes_iff_mem_closure.mpr
      (by rw [hcl', ← hcl]; exact subset_closure rfl)
    exact (inseparable_iff_specializes_and.mpr ⟨a2, a1⟩).eq
  subst hCC'
  rw [genericFiberDegree_single g P₁ hP₁, hd₁] at hgd₁
  rw [genericFiberDegree_single g P₂ hP₂, hd₂] at hgd₂
  -- every contracted curve is numerically a multiple of `C'`
  obtain ⟨HV, hHVi, hHVa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety
    hg.isProjectiveVariety
  have hpos := degree_pos_of_isAmple' C' HV hHVa
  refine exists_qLinearlyEquivalent_pullback sV sT hdimV hQ K hK B ε hklt g hg hdimT
    (D₁ - D₂) fun γ hγ => ?_
  have hγc := eq_smul_of_degree_pullback_eq_zero sV sT g hgc.comp_eq
    hg.relativePicardNumber_eq_one C' hCc HV hpos (OneCycle.numericalClass sV (γ.cycle ℝ))
    fun M _ => by
      rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle,
        γ.degree_pullback_eq_zero_of_isContractedBy g hgc.comp_eq hγ M, Int.cast_zero]
  have hform := congrArg (QDivisor.curveForm sV (D₁ - D₂) (hqc _)) hγc
  rw [map_smul, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle] at hform
  have hsub : (D₁ - D₂).intersectionNumber k sV C'.ι C'.dim_le (hqc _) = 0 := by
    have e : D₁ - D₂ = D₁ + (-1 : ℚ) • D₂ := by rw [neg_one_smul]; abel
    rw [intersectionNumber_congr sV C'.ι C'.dim_le (hqc _) (hqc _) e,
      QDivisor.intersectionNumber_add' k sV C'.ι C'.dim_le _ _ (hqc _) (hqc _) (hqc _),
      intersectionNumber_smul sV C'.ι C'.dim_le D₂ (hqc _) (-1) (hqc _), ← hgd₁, ← hgd₂]
    push_cast; ring
  rw [hsub] at hform
  simp only [Rat.cast_zero, smul_zero] at hform
  exact_mod_cast hform

/-- **A global log pluricanonical form with vertical adjoint divisor.** Some rational
`m`-canonical form `Ω₀` on `V` has `div Ω₀ + mB` equal to `m` times the pull-back of a
`ℚ`-Cartier divisor of `T`. -/
private theorem exists_rationalPluriForm_ordForm_add_eq_pullback
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T]
    (hdimV : topologicalKrullDim V = 2) (hQ : IsQFactorial sV)
    (K : Divisor V) (hK : K.IsCanonicalDivisor sV 2)
    (B : QDivisor V) (hlc : MMP.Intersection.IsLogCanonicalPair sV B)
    (ε : ℚ) (hε : 0 < ε ∧ ε < 1)
    (hklt : IsKltPair sV (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))
    (g : V ⟶ T) [IsDominant g]
    (hg : IsMoriFibreSpace sV sT K (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)) g)
    (hdimT : topologicalKrullDim T = 1)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sV g
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)))
    [IsLocallyNoetherian T] [IsNormal T] :
    ∃ (m : ℕ) (_ : 0 < m) (Ω₀ : RationalPluriForms sV 2 m) (M : QDivisor T) (hM : M.IsQCartier)
      (hMf : ∀ Z : irreducibleComponents V, g (componentGenericPoint V Z) ∉ M.supp),
      Ω₀ ≠ 0 ∧ ∀ Γ : Mori.PrimeDivisor V,
        (Γ.ordForm Ω₀ : ℚ) + m * B Γ = m * (M.pullback hM hMf) Γ := by
  classical
  obtain ⟨hVv, hVproj⟩ := (Mori.isProjectiveVariety_iff k sV).mp hg.isProjectiveVariety
  have : IsProper sV := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hVproj).2
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  set Kq : QDivisor V := Divisor.toQDivisor K
  have hqc : ∀ D : QDivisor V, D.IsQCartier := isQCartier_of_isQFactorial sV hQ
  have hKB0 : ∀ γ : ProperCurve sV, γ.IsContractedBy g →
      (Kq + B).intersectionNumber k sV γ.ι γ.dim_le (hqc _) = 0 :=
    intersectionNumber_eq_zero_of_isNumericallyTrivialOver sV hQ hnum
  obtain ⟨M, hM, hMf, m, hm, φ, hφ⟩ := exists_qLinearlyEquivalent_pullback sV sT hdimV hQ K hK
    B ε hklt g hg hdimT (Kq + B) hKB0
  set C : Divisor V := (m : ℤ) • K - principalDivisor φ
  obtain ⟨Ω₀, hΩ0, hΩ⟩ := exists_ordForm_eq_of_principal ⟨hVv, inferInstance⟩ hK m C φ
    (fun Γ => by
      simp only [C, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
        coeff_principalDivisor, smul_eq_mul]
      ring)
  refine ⟨m, hm, Ω₀, M, hM, hMf, hΩ0, fun Γ => ?_⟩
  have h1 := congrArg (fun D : QDivisor V => D Γ) hφ
  simp only [Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.add_apply, zsmul_eq_mul] at h1
  have h2 : ((Divisor.toQDivisor (principalDivisor φ)) Γ : ℚ) = (Γ.ord φ : ℚ) := by
    change DivisorWithCoeffs.coeff (Divisor.toQDivisor (principalDivisor φ)) Γ = _
    rw [Divisor.coeff_toQDivisor, coeff_principalDivisor]
  have h3 : (Kq Γ : ℚ) = (K.coeff Γ : ℚ) := by
    change DivisorWithCoeffs.coeff (Divisor.toQDivisor K) Γ = _
    rw [Divisor.coeff_toQDivisor]
  rw [hΩ Γ]
  simp only [C, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
    coeff_principalDivisor, smul_eq_mul]
  rw [h2, h3] at h1
  push_cast
  change ((m : ℚ) * (K.coeff Γ : ℚ) - (Γ.ord φ : ℚ)) + m * B Γ = m * _
  push_cast at h1
  linear_combination h1

section ResidueAlgebra

open exteriorPower

variable {k : Type*} [Field k] {O : Type*} [CommRing O] [IsDomain O] [Algebra k O]
  {K : Type*} [Field K] [Algebra k K] [Algebra O K] [IsScalarTower k O K] [IsFractionRing O K]
  {L : Type*} [Field L] [Algebra k L] [Algebra O L] [IsScalarTower k O L]

private theorem ιMulti_cons_add {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (v w : M) (f : Fin n → M) :
    ιMulti R (n + 1) (Fin.cons (v + w) f) =
      ιMulti R (n + 1) (Fin.cons v f) + ιMulti R (n + 1) (Fin.cons w f) := by
  have := (ιMulti R (n + 1)).map_update_add (Fin.cons 0 f) 0 v w
  simpa only [Fin.update_cons_zero] using this

private theorem ιMulti_cons_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (c : R) (v : M) (f : Fin n → M) :
    ιMulti R (n + 1) (Fin.cons (c • v) f) = c • ιMulti R (n + 1) (Fin.cons v f) := by
  have := (ιMulti R (n + 1)).map_update_smul (Fin.cons 0 f) 0 c v
  simpa only [Fin.update_cons_zero] using this

/-- **Comparison of a twisted logarithmic frame.** For a unit `u`, the frame
`(ut₀)⁻¹ d(ut₀) ∧ dx` is `c` times `t₀⁻¹ dt₀ ∧ dx` with `c ∈ O`, `c̄ = 1`, when `dx̄ ≠ 0`. -/
private theorem exists_frame_unit_eq [Module.Free O Ω[O⁄k]] [ValuationRing O]
    (hline : Module.finrank K (⋀[K]^2 Ω[K⁄k]) = 1)
    (hπ : Function.Surjective (algebraMap O L)) {t₀ : O} (ht₀ : algebraMap O L t₀ = 0)
    {r : Ω[O⁄k] →ₗ[O] O} (hr : r (KaehlerDifferential.D k O t₀) = 1) {u : O} (hu : IsUnit u)
    (x : O) (hx : ιMulti L 1 (fun _ : Fin 1 => KaehlerDifferential.D k L (algebraMap O L x)) ≠ 0) :
    ∃ c : O, algebraMap O L c = 1 ∧
      (algebraMap O K (u * t₀))⁻¹ • ιMulti K 2 (Fin.cons (KaehlerDifferential.D k K
          (algebraMap O K (u * t₀))) fun _ : Fin 1 => KaehlerDifferential.D k K (algebraMap O K x)) =
        algebraMap O K c • ((algebraMap O K (1 * t₀))⁻¹ • ιMulti K 2 (Fin.cons
          (KaehlerDifferential.D k K (algebraMap O K (1 * t₀)))
            fun _ : Fin 1 => KaehlerDifferential.D k K (algebraMap O K x))) := by
  have hloc : ∀ c : O, algebraMap O L c = 1 → IsUnit c := by
    intro c hc
    by_contra hnu
    have hker : RingHom.ker (algebraMap O L) = IsLocalRing.maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hπ)
    have hm : c ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← hker, RingHom.mem_ker, hc] at hm
    exact one_ne_zero hm
  have hcancel : ∀ c : O, ιMulti L 1 (fun _ : Fin 1 => KaehlerDifferential.D k L
      (algebraMap O L x)) = algebraMap O L c • ιMulti L 1 (fun _ : Fin 1 =>
        KaehlerDifferential.D k L (algebraMap O L x)) → algebraMap O L c = 1 := by
    intro c h
    by_contra hc
    apply hx
    have h2 : (1 - algebraMap O L c) • ιMulti L 1 (fun _ : Fin 1 => KaehlerDifferential.D k L
        (algebraMap O L x)) = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hc))
  rcases exists_frame_comparison (K := K) (L := L) (e := 1) hline hπ ht₀ hr
    isUnit_one hu (fun _ => x) (fun _ => x) with ⟨c, hcK, hcL⟩ | ⟨c, hcK, hcL⟩
  · exact ⟨c, hcancel c hcL, hcK⟩
  · have h1 := hcancel c hcL
    obtain ⟨c', hc'⟩ := (hloc c h1).exists_left_inv
    refine ⟨c', ?_, ?_⟩
    · have := congrArg (algebraMap O L) hc'
      rwa [map_mul, h1, mul_one, map_one] at this
    · beta_reduce at hcK
      rw [hcK, smul_smul, ← map_mul, hc', map_one, one_smul]

private theorem inv_smul_D_mul_zpow {u t : K} (hu : u ≠ 0) (ht : t ≠ 0) (a : ℤ) :
    (u * t ^ a)⁻¹ • KaehlerDifferential.D k K (u * t ^ a) =
      (a : K) • (t⁻¹ • KaehlerDifferential.D k K t) + u⁻¹ • KaehlerDifferential.D k K u := by
  rw [Derivation.leibniz, Derivation.leibniz_zpow, ← Int.cast_smul_eq_zsmul K,
    zpow_sub_one₀ ht]
  have hta : t ^ a ≠ 0 := zpow_ne_zero _ ht
  match_scalars <;> field_simp

/-- **The residue frame of a logarithmic 2-form.** For `f = u t₀^a`, `u` a unit, and `x` with
`dx̄ ≠ 0`, the form `q f⁻¹ df ∧ dx` is `G · t₀⁻¹ dt₀ ∧ dx` with `G ∈ O` and `Ḡ = q a`. -/
private theorem exists_dlog_frame_eq [Module.Free O Ω[O⁄k]] [ValuationRing O]
    (hline : Module.finrank K (⋀[K]^2 Ω[K⁄k]) = 1)
    (hπ : Function.Surjective (algebraMap O L)) {t₀ : O} (ht₀ : algebraMap O L t₀ = 0)
    {r : Ω[O⁄k] →ₗ[O] O} (hr : r (KaehlerDifferential.D k O t₀) = 1) {u : O} (hu : IsUnit u)
    (a : ℤ) (x : O)
    (hx : ιMulti L 1 (fun _ : Fin 1 => KaehlerDifferential.D k L (algebraMap O L x)) ≠ 0)
    (q : k) :
    ∃ G : O, algebraMap O L G = algebraMap k L q * (a : L) ∧
      (algebraMap k K q * (algebraMap O K u * algebraMap O K t₀ ^ a)⁻¹) •
          ιMulti K 2 (Fin.cons (KaehlerDifferential.D k K
            (algebraMap O K u * algebraMap O K t₀ ^ a))
            fun _ : Fin 1 => KaehlerDifferential.D k K (algebraMap O K x)) =
        algebraMap O K G • ((algebraMap O K t₀)⁻¹ • ιMulti K 2 (Fin.cons
          (KaehlerDifferential.D k K (algebraMap O K t₀))
            fun _ : Fin 1 => KaehlerDifferential.D k K (algebraMap O K x))) := by
  obtain ⟨c, hc1, hcK⟩ := exists_frame_unit_eq (K := K) hline hπ ht₀ hr hu x hx
  simp only [one_mul] at hcK
  have ht0 : t₀ ≠ 0 := by
    rintro rfl
    simp at hr
  have huH : algebraMap O K u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hu.ne_zero
  have htH : algebraMap O K t₀ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr ht0
  set uH := algebraMap O K u
  set tH := algebraMap O K t₀
  set xH : Fin 1 → Ω[K⁄k] := fun _ => KaehlerDifferential.D k K (algebraMap O K x)
  set fr := ιMulti K 2 (Fin.cons (tH⁻¹ • KaehlerDifferential.D k K tH) xH)
  have hfr : tH⁻¹ • ιMulti K 2 (Fin.cons (KaehlerDifferential.D k K tH) xH) = fr :=
    (ιMulti_cons_smul _ _ _).symm
  have h1 : ιMulti K 2 (Fin.cons (uH⁻¹ • KaehlerDifferential.D k K uH) xH) =
      (algebraMap O K c - 1) • fr := by
    have e := hcK
    rw [hfr, map_mul, ← ιMulti_cons_smul] at e
    have e2 := inv_smul_D_mul_zpow (k := k) huH htH 1
    rw [zpow_one, Int.cast_one, one_smul] at e2
    rw [e2, ιMulti_cons_add] at e
    rw [sub_smul, one_smul, ← e]
    abel
  refine ⟨algebraMap k O q * ((a : O) + c - 1), ?_, ?_⟩
  · rw [map_mul, map_sub, map_add, hc1, ← IsScalarTower.algebraMap_apply]
    simp
  · rw [← smul_smul, ← ιMulti_cons_smul, inv_smul_D_mul_zpow (k := k) huH htH a,
      ιMulti_cons_add, ιMulti_cons_smul, h1, hfr]
    rw [map_mul, map_sub, map_add, map_intCast, map_one, ← IsScalarTower.algebraMap_apply]
    change (algebraMap k K q) • ((a : K) • fr + (algebraMap O K c - 1) • fr) = _
    rw [← add_smul, smul_smul]
    congr 1
    ring

section Scheme

variable {k₀ : Type} [Field k₀] [PerfectField k₀] {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of k₀)}
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] {j : T ⟶ Y}

/-- A nonzero rational function is a unit times a power of a uniformizer `ϖ` (of order one) in the
local ring of a codimension-one point. -/
private theorem exists_isUnit_eq_mul_zpow {z : Y} (hz : Order.coheight z = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk z)] {ϖ : Y.presheaf.stalk z}
    (hϖ : Y.ord (algebraMap _ Y.functionField ϖ) z = 1) {f : Y.functionField} (hf : f ≠ 0) :
    ∃ u : Y.presheaf.stalk z, IsUnit u ∧
      f = algebraMap _ Y.functionField u * algebraMap _ Y.functionField ϖ ^ Y.ord f z := by
  have hϖ0 : algebraMap (Y.presheaf.stalk z) Y.functionField ϖ ≠ 0 := by
    intro h; rw [h] at hϖ; simp at hϖ
  have hpow : algebraMap (Y.presheaf.stalk z) Y.functionField ϖ ^ Y.ord f z ≠ 0 :=
    zpow_ne_zero _ hϖ0
  have h1 : Y.ord (algebraMap _ Y.functionField ϖ ^ Y.ord f z) z = Y.ord f z := by
    rw [MMP.Mori.ord_zpow z hϖ0, hϖ, mul_one]
  have h2 := (Scheme.ord_eq_iff hz hpow).mp h1
  have h3 := (Scheme.ord_eq_iff hz hf).mp rfl
  obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq (R := Y.presheaf.stalk z)
    (algebraMap _ Y.functionField ϖ ^ Y.ord f z) f (h2.trans h3.symm)
  refine ⟨u, u.isUnit, hu.symm.trans ?_⟩
  rw [Units.smul_def, Algebra.smul_def]

end Scheme

end ResidueAlgebra

section ResidueGeneral

variable {k : Type} [Field k] {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] {j : T ⟶ Y}

/-- If `j` induces an isomorphism of residue fields at the generic point, the restriction
`𝒪_{Y, j(η)} → k(T)` is surjective. -/
private theorem stalkMap_surjective_of_isIso_residueFieldMap
    (hres : IsIso (j.residueFieldMap (genericPoint T))) :
    Function.Surjective (j.stalkMap (genericPoint T)).hom := by
  have hF : IsField (T.presheaf.stalk (genericPoint T)) := Field.toIsField T.functionField
  have hm := IsLocalRing.isField_iff_maximalIdeal_eq.mp hF
  have hinj : Function.Injective (T.residue (genericPoint T)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.residue_eq_zero_iff a).mp ha
    rwa [hm] at this
  have hR := (ConcreteCategory.isIso_iff_bijective _).mp hres
  intro b
  obtain ⟨c, hc⟩ := hR.2 (T.residue (genericPoint T) b)
  obtain ⟨a, rfl⟩ := Y.residue_surjective _ c
  refine ⟨a, hinj ?_⟩
  have hcomm := congrArg (fun φ => (CommRingCat.Hom.hom φ) a)
    (Scheme.residue_residueFieldMap j (genericPoint T))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hcomm
  rw [← hc]
  exact hcomm.symm

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The restriction `𝒪_{Y,j(η)} → k(T)` is a `k`-algebra map. -/
private theorem stalkMap_isScalarTower :
    letI := stalkAlgebra sY (j (genericPoint T))
    letI := functionFieldAlgebra (j ≫ sY)
    letI : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
      (j.stalkMap (genericPoint T)).hom.toAlgebra
    IsScalarTower k (Y.presheaf.stalk (j (genericPoint T))) T.functionField := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ sY).appTop ≫
        T.presheaf.germ ⊤ (genericPoint T) (TopologicalSpace.Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫
        Y.presheaf.germ ⊤ (j (genericPoint T)) (TopologicalSpace.Opens.mem_top _)) ≫
        j.stalkMap (genericPoint T) := by
    simp only [Category.assoc, Scheme.Hom.germ_stalkMap, Scheme.Hom.comp_appTop]
    rfl
  exact congrArg CommRingCat.Hom.hom h

variable [PerfectField k] [LocallyOfFiniteType sY] [LocallyOfFiniteType (j ≫ sY)]

/-- **Uniformizers along a prime divisor**, for a morphism `j` surjective on stalks at the generic
point. -/
private theorem exists_uniformizer_of_surjective (P : Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint)
    (hsurj : Function.Surjective (j.stalkMap (genericPoint T)).hom) :
    letI := stalkAlgebra sY (j (genericPoint T))
    letI := functionFieldAlgebra (j ≫ sY)
    letI : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
      (j.stalkMap (genericPoint T)).hom.toAlgebra
    ∃ (ϖ : Y.presheaf.stalk (j (genericPoint T)))
      (r : Ω[(Y.presheaf.stalk (j (genericPoint T)))⁄k] →ₗ[Y.presheaf.stalk (j (genericPoint T))]
        Y.presheaf.stalk (j (genericPoint T))),
      algebraMap _ T.functionField ϖ = 0 ∧ r (KaehlerDifferential.D k _ ϖ) = 1 ∧
      ∀ t : Y.presheaf.stalk (j (genericPoint T)),
        Y.ord (algebraMap _ Y.functionField t) (j (genericPoint T)) = 1 →
          ∃ u, IsUnit u ∧ t = u * ϖ := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  obtain ⟨hdvr, hfree, hfin, hsm, hcoh, -⟩ := stalk_facts_of_eq_genericPoint (sY := sY) P hP
  have htow := stalkMap_isScalarTower (sY := sY) (j := j)
  have := essFiniteType_functionField (sX := j ≫ sY)
  obtain ⟨ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk (j (genericPoint T)))
  have hker : RingHom.ker (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) =
      Ideal.span {ϖ} :=
    (IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)).trans
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ)
  have hϖ2 :
      ϖ ∉ RingHom.ker (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) ^ 2 := by
    rw [hker, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have h1 : ϖ * 1 = ϖ * (ϖ * c) := by rw [mul_one, ← mul_assoc, ← pow_two]; exact hc
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one c (mul_left_cancel₀ hϖ.ne_zero h1).symm)
  obtain ⟨r, hr⟩ := exists_retraction_D (k := k) hsurj (hker ▸ Ideal.mem_span_singleton_self ϖ) hϖ2
  refine ⟨ϖ, r, RingHom.mem_ker.mp (hker ▸ Ideal.mem_span_singleton_self ϖ), hr, fun t ht => ?_⟩
  have ht0 : algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField t ≠ 0 := by
    intro h
    rw [h] at ht
    have := congrFun Scheme.ord_zero (j (genericPoint T))
    simp only [Pi.zero_apply] at this
    omega
  have h1 := (Scheme.ord_eq_iff hcoh ht0).mp ht
  have h2 : Ring.ordFrac (Y.presheaf.stalk (j (genericPoint T)))
      (algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField ϖ) = WithZero.exp 1 :=
    Ring.ordFrac_irreducible hϖ
  obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq (R := (Y.presheaf.stalk (j (genericPoint T))))
    (algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField ϖ)
    (algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField t) (h2.trans h1.symm)
  refine ⟨u, u.isUnit,
    IsFractionRing.injective (Y.presheaf.stalk (j (genericPoint T))) Y.functionField ?_⟩
  rw [← hu, map_mul, Units.smul_def, Algebra.smul_def]

/-- **Uniqueness of the Poincaré residue** along a morphism surjective on stalks at the generic
point onto a prime divisor. -/
private theorem IsPoincareResidue.unique_of_surjective (P : Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint)
    (hsurj : Function.Surjective (j.stalkMap (genericPoint T)).hom)
    {n m : ℕ} {τ : RationalPluriForms sY (n + 1) m} {ρ ρ' : RationalPluriForms (j ≫ sY) n m}
    (h : IsPoincareResidue sY j n m τ ρ) (h' : IsPoincareResidue sY j n m τ ρ') : ρ = ρ' := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  have := isScalarTower_stalk_functionField sY (j (genericPoint T))
  obtain ⟨hdvr, hfree, -, -, -, -⟩ := stalk_facts_of_eq_genericPoint (sY := sY) P hP
  have htow := stalkMap_isScalarTower (sY := sY) (j := j)
  obtain ⟨ϖ, r, hϖ0, hr, hunif⟩ := exists_uniformizer_of_surjective (sY := sY) P hP hsurj
  obtain ⟨t₁, g₁, x₁, ht₁, hτ₁, rfl⟩ := h
  obtain ⟨t₂, g₂, x₂, ht₂, hτ₂, rfl⟩ := h'
  obtain ⟨u₁, hu₁, rfl⟩ := hunif t₁ ht₁
  obtain ⟨u₂, hu₂, rfl⟩ := hunif t₂ ht₂
  exact logPluriResidue_eq_of_logPluriForm_eq hsurj hϖ0 hr hu₁ hu₂ x₁ x₂ (hτ₁.symm.trans hτ₂)

end ResidueGeneral

section BisectionB11

open exteriorPower

variable {k₀ : Type} [Field k₀] [PerfectField k₀] {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of k₀)}
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] {j : T ⟶ Y}

/-- **Residues of logarithmic 2-forms along a branch.** Along a morphism `j : T ⟶ Y` onto a
prime divisor `P` of a normal surface, surjective on stalks at the generic point, the Poincaré
residue of `c (q f⁻¹ df ∧ dx)^{⊗m}` is `c̄ (q ord_P f)^m (dx̄)^{⊗m}`, when `dx̄ ≠ 0`. -/
private theorem isPoincareResidue_smul_formPow_dlog_of_surjective [LocallyOfFiniteType sY]
    [LocallyOfFiniteType (j ≫ sY)]
    (P : Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    (hsurj : Function.Surjective (j.stalkMap (genericPoint T)).hom)
    (hdim : topologicalKrullDim Y = 2) (q : k₀) {f : Y.functionField} (hf : f ≠ 0)
    (x c : Y.presheaf.stalk (j (genericPoint T)))
    (hx : letI := functionFieldAlgebra (j ≫ sY)
      KaehlerDifferential.D k₀ T.functionField ((j.stalkMap (genericPoint T)).hom x) ≠ 0)
    (m : ℕ) :
    letI := functionFieldAlgebra sY
    letI := functionFieldAlgebra (j ≫ sY)
    IsPoincareResidue sY j 1 m
      (algebraMap _ Y.functionField c • formPow ((algebraMap k₀ Y.functionField q * f⁻¹) •
        ιMulti Y.functionField 2 (Fin.cons (KaehlerDifferential.D k₀ Y.functionField f)
          fun _ : Fin 1 => KaehlerDifferential.D k₀ Y.functionField
            (algebraMap _ Y.functionField x))) m)
      (((j.stalkMap (genericPoint T)).hom c * (algebraMap k₀ T.functionField q *
          (Y.ord f (j (genericPoint T)) : T.functionField)) ^ m) •
        formPow (ιMulti T.functionField 1 fun _ : Fin 1 => KaehlerDifferential.D k₀
          T.functionField ((j.stalkMap (genericPoint T)).hom x)) m) := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  have := isScalarTower_stalk_functionField sY (j (genericPoint T))
  obtain ⟨hdvr, hfree, -, -, hcoh, -⟩ := stalk_facts_of_eq_genericPoint (sY := sY) P hP
  have htow := stalkMap_isScalarTower (sY := sY) (j := j)
  obtain ⟨ϖ, r, hϖ0, hr, hunif⟩ := exists_uniformizer_of_surjective (sY := sY) P hP hsurj
  have hordunit : ∀ u : Y.presheaf.stalk (j (genericPoint T)), IsUnit u →
      Y.ord (algebraMap _ Y.functionField u) (j (genericPoint T)) = 0 := by
    intro u hu
    have hne : algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField u ≠ 0 :=
      (hu.map _).ne_zero
    rw [Scheme.ord_eq_iff hcoh hne, ofAdd_zero]
    have : Ring.KrullDimLE 1 (Y.presheaf.stalk (j (genericPoint T))) :=
      krullDimLE_of_coheight_le hcoh.le
    exact Ring.ordFrac_of_isUnit hu
  have hϖord : Y.ord (algebraMap _ Y.functionField ϖ) (j (genericPoint T)) = 1 := by
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible
      (Y.presheaf.stalk (j (genericPoint T)))
    have hp0 : algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField p ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hp.ne_zero
    have hpord : Y.ord (algebraMap _ Y.functionField p) (j (genericPoint T)) = 1 :=
      (Scheme.ord_eq_iff hcoh hp0).mpr (Ring.ordFrac_irreducible hp)
    obtain ⟨u₁, hu₁, hpu⟩ := hunif p hpord
    have hu0 := hordunit u₁ hu₁
    have hu₁0 : algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField u₁ ≠ 0 :=
      (hu₁.map _).ne_zero
    have hϖ0' : algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField ϖ ≠ 0 := by
      intro h0; apply hp0; rw [hpu, map_mul, h0, mul_zero]
    rw [hpu, map_mul, Scheme.ord_mul hu₁0 hϖ0', hu0, zero_add] at hpord
    exact hpord
  obtain ⟨u, hu, hfu⟩ := exists_isUnit_eq_mul_zpow hcoh hϖord hf
  obtain ⟨b₀⟩ := exists_basis_topForms (sX := sY) (d := 2) (by rw [hdim]; norm_cast)
  have hline : Module.finrank Y.functionField (⋀[Y.functionField]^2 Ω[Y.functionField⁄k₀]) =
      1 := by rw [Module.finrank_eq_card_basis b₀, Fintype.card_unit]
  have hx' : ιMulti T.functionField 1 (fun _ : Fin 1 => KaehlerDifferential.D k₀ T.functionField
      (algebraMap _ T.functionField x)) ≠ 0 := by
    intro h0
    apply hx
    have := congrArg (exteriorPower.oneEquiv T.functionField _) h0
    simp only [exteriorPower.oneEquiv_ιMulti, map_zero] at this
    exact this
  obtain ⟨G, hG, hGK⟩ := exists_dlog_frame_eq (K := Y.functionField) (L := T.functionField)
    hline hsurj hϖ0 hr hu (Y.ord f (j (genericPoint T))) x hx' q
  refine ⟨ϖ, c * G ^ m, fun _ => x, hϖord, ?_, ?_⟩
  · rw [hfu, hGK, formPow_smul, smul_smul, ← map_pow, ← map_mul]
    rfl
  · rw [map_mul, map_pow]
    change _ = (algebraMap _ T.functionField c * algebraMap _ T.functionField G ^ m) • _
    rw [hG]
    rfl

end BisectionB11

section CurveCrepant

open scoped WithZero

variable {k : Type} [Field k] [PerfectField k]

/-- On a curve, every divisor over it has the valuation of a prime divisor. -/
private theorem exists_primeDivisor_valuation_eq_of_dim_eq_one {N : Scheme.{0}} {sN : N ⟶ Spec (.of k)}
    [IsIntegral N] [IsLocallyNoetherian N] [IsNormal N] (hN : IsNormalVariety k sN)
    (hdim : topologicalKrullDim N = 1) (D : DivisorOver k sN) :
    ∃ P : Mori.PrimeDivisor N, D.valuation = (DivisorOver.ofPrimeDivisor k hN P).valuation := by
  by_contra h
  push Not at h
  have h2 := (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hN D).mpr h
  rw [MMP.Positivity.DivisorOver.codimension_center] at h2
  letI : N.Over (Spec (.of k)) := ⟨sN⟩
  have : LocallyOfFiniteType (N ↘ Spec (.of k)) := hN.1.toLocallyOfFiniteType
  have hpure : MMP.Intersection.IsPureDimensional N 1 := by
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [(Homeomorph.Set.univ N).isHomeomorph.topologicalKrullDim_eq, hdim]
    rfl
  have h3 := MMP.Intersection.height_add_coheight_eq_of_isPureDimensional k hpure
    (D.f D.E.genericPoint)
  have h4 : (2 : ℕ∞) ≤ Order.height (D.f D.E.genericPoint) + Order.coheight (D.f D.E.genericPoint) :=
    h2.trans le_add_self
  rw [h3] at h4
  norm_num at h4

/-- **Isomorphisms of curve pairs transport log discrepancies.** -/
private theorem hasLogDiscrepancy_comap_of_isIso {N₁ N₂ : Scheme.{0}} {s₁ : N₁ ⟶ Spec (.of k)}
    {s₂ : N₂ ⟶ Spec (.of k)} [IsIntegral N₁] [IsLocallyNoetherian N₁] [IsNormal N₁]
    [IsIntegral N₂] [IsLocallyNoetherian N₂] [IsNormal N₂]
    (hN₁ : IsNormalVariety k s₁) (hN₂ : IsNormalVariety k s₂)
    (hdim₁ : topologicalKrullDim N₁ = 1) (hdim₂ : topologicalKrullDim N₂ = 1)
    (α : N₁ ⟶ N₂) [IsIso α] (hα : α ≫ s₂ = s₁) {Θ₁ : QDivisor N₁} {Θ₂ : QDivisor N₂}
    (hP₁ : MMP.Mori.IsPair s₁ Θ₁) (hP₂ : MMP.Mori.IsPair s₂ Θ₂)
    (hΘ : ∀ (P : Mori.PrimeDivisor N₁) (Q : Mori.PrimeDivisor N₂),
      Q.genericPoint = α P.genericPoint → Θ₂.coeff Q = Θ₁.coeff P)
    (σ : FunctionFieldEquiv s₁ s₂)
    (hσ : letI := functionFieldAlgebra s₁; letI := functionFieldAlgebra s₂
      ∀ a, σ a = functionFieldMap α a)
    (v : Valuation N₁.functionField ℤᵐ⁰) (a : ℝ) (h : HasLogDiscrepancy s₁ Θ₁ v a) :
    letI := functionFieldAlgebra s₁
    letI := functionFieldAlgebra s₂
    HasLogDiscrepancy s₂ Θ₂ (v.comap σ.toRingEquiv.toRingHom) a := by
  let := functionFieldAlgebra s₁
  let := functionFieldAlgebra s₂
  obtain ⟨n, D, hDv, hD⟩ := h
  obtain ⟨P, hPv⟩ := exists_primeDivisor_valuation_eq_of_dim_eq_one hN₁ hdim₁ D
  let D' : DivisorOver k s₂ :=
    { Y := N₁, f := α, isNormalVariety := by rw [hα]; exact hN₁
      isBirationalMorphism := isBirationalMorphism_of_isIso _, E := P }
  have hD'v : D'.valuation = v.comap σ.toRingEquiv.toRingHom := by
    ext b
    rw [← hDv, hPv]
    change P.valuationOver α b = P.valuationOver (𝟙 N₁) (σ b)
    rw [PrimeDivisor.valuationOver_apply, PrimeDivisor.valuationOver_apply, hσ,
      functionFieldMap_id_apply]
  obtain ⟨Q, hQv⟩ := exists_primeDivisor_valuation_eq_of_dim_eq_one hN₂ hdim₂ D'
  have hQ : α P.genericPoint = Q.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hN₂.1 hQv
  obtain ⟨-, n₂, K₂, hK₂, -⟩ := id hP₂
  obtain ⟨-, n₁, K₁, hK₁, -⟩ := id hP₁
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP₂ hK₂ D'
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (inferInstance : IsProper α)
  obtain ⟨cQ, hcQ⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP₂ hK₂
    (DivisorOver.ofPrimeDivisor k hN₂ Q)
  have hlogQ := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hcQ
    (inferInstance : IsProper (𝟙 N₂))
  obtain ⟨cP, hcP⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP₁ hK₁
    (DivisorOver.ofPrimeDivisor k hN₁ P)
  have hlogP := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hcP
    (inferInstance : IsProper (𝟙 N₁))
  have e1 := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog hlogQ hQv
  have e2 := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hD hlogP hPv
  have e3 := hcQ.eq_neg_coeff_of_ofPrimeDivisor hN₂
  have e4 := hcP.eq_neg_coeff_of_ofPrimeDivisor hN₁
  have e5 := hΘ P Q hQ.symm
  refine ⟨n₂, D', hD'v, ?_⟩
  convert hlog using 1
  rw [e2, e1, e3, e4, e5]

/-- `functionFieldMap` only depends on the morphism. -/
private theorem functionFieldMap_congr_hom {A B : Scheme.{0}} [IsIntegral A] [IsIntegral B] {f g : A ⟶ B}
    [IsDominant f] [IsDominant g] (h : f = g) (t : B.functionField) :
    functionFieldMap f t = functionFieldMap g t := by
  subst h; rfl

/-- **Isomorphisms of curve pairs are crepant.** -/
private theorem isCrepantBirationalMap_of_isIso {N₁ N₂ : Scheme.{0}} {s₁ : N₁ ⟶ Spec (.of k)}
    {s₂ : N₂ ⟶ Spec (.of k)} [IsIntegral N₁] [IsLocallyNoetherian N₁] [IsNormal N₁]
    [IsIntegral N₂] [IsLocallyNoetherian N₂] [IsNormal N₂]
    (hN₁ : IsNormalVariety k s₁) (hN₂ : IsNormalVariety k s₂)
    (hdim₁ : topologicalKrullDim N₁ = 1) (hdim₂ : topologicalKrullDim N₂ = 1)
    (α : N₁ ⟶ N₂) [IsIso α] (hα : α ≫ s₂ = s₁) {Θ₁ : QDivisor N₁} {Θ₂ : QDivisor N₂}
    (hP₁ : MMP.Mori.IsPair s₁ Θ₁) (hP₂ : MMP.Mori.IsPair s₂ Θ₂)
    (hΘ : ∀ (P : Mori.PrimeDivisor N₁) (Q : Mori.PrimeDivisor N₂),
      Q.genericPoint = α P.genericPoint → Θ₂.coeff Q = Θ₁.coeff P)
    (σ : FunctionFieldEquiv s₁ s₂)
    (hσ : letI := functionFieldAlgebra s₁; letI := functionFieldAlgebra s₂
      ∀ a, σ a = functionFieldMap α a) :
    IsCrepantBirationalMap s₁ s₂ Θ₁ Θ₂ σ := by
  let := functionFieldAlgebra s₁
  let := functionFieldAlgebra s₂
  intro v a
  refine ⟨hasLogDiscrepancy_comap_of_isIso hN₁ hN₂ hdim₁ hdim₂ α hα hP₁ hP₂ hΘ σ hσ v a,
    fun h => ?_⟩
  have hα' : inv α ≫ s₁ = s₂ := by rw [← hα, IsIso.inv_hom_id_assoc]
  have hσ' : ∀ a, σ.symm a = functionFieldMap (inv α) a := by
    intro b
    apply σ.injective
    rw [AlgEquiv.apply_symm_apply, hσ, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      functionFieldMap_congr_hom (IsIso.hom_inv_id α), functionFieldMap_id_apply]
  have h' := hasLogDiscrepancy_comap_of_isIso hN₂ hN₁ hdim₂ hdim₁ (inv α) hα' hP₂ hP₁
    (fun Q P hP => by
      refine (hΘ P Q ?_).symm
      rw [hP, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl) σ.symm hσ' _ a h
  have hv : (v.comap σ.toRingEquiv.toRingHom).comap σ.symm.toRingEquiv.toRingHom = v := by
    ext x
    change v (σ (σ.symm x)) = v x
    rw [AlgEquiv.apply_symm_apply]
  rwa [hv] at h'

end CurveCrepant

section Descent

/-- A pull-back of a nonzero rational function from the base has order zero along a horizontal
prime divisor. -/
private theorem ord_functionFieldMap_eq_zero {V T : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V]
    [IsIntegral T] (g : V ⟶ T) [IsDominant g] (Γ : Mori.PrimeDivisor V)
    (hΓ : g Γ.genericPoint = genericPoint T) {a : T.functionField} (ha : a ≠ 0) :
    V.ord (functionFieldMap g a) Γ.genericPoint = 0 := by
  have hF : IsField (T.presheaf.stalk (g Γ.genericPoint)) := by
    rw [hΓ]; exact Field.toIsField T.functionField
  let a' : T.presheaf.stalk (g Γ.genericPoint) :=
    (T.presheaf.stalkSpecializes (show g Γ.genericPoint ⤳ genericPoint T by rw [hΓ])).hom a
  have hspec : algebraMap (T.presheaf.stalk (g Γ.genericPoint)) T.functionField a' = a := by
    change (T.presheaf.stalkSpecializes _ ≫ T.presheaf.stalkSpecializes _).hom a = a
    rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have ha' : a' ≠ 0 := by
    intro h0; apply ha; rw [← hspec, h0, map_zero]
  have hu : IsUnit ((g.stalkMap Γ.genericPoint).hom a') := by
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel ha'
    exact (IsUnit.of_mul_eq_one b hb).map _
  rw [← hspec, MMP.Mori.functionFieldMap_algebraMap_stalk g Γ.genericPoint a']
  exact Γ.ord_algebraMap_of_isUnit hu

/-- **Rational functions without horizontal zeros or poles come from the base.** -/
private theorem exists_functionFieldMap_eq_of_forall_ord_eq_zero {V T : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsIntegral T]
    (g : V ⟶ T) [IsDominant g] (hO : ∀ U : T.Opens, IsIso (g.app U))
    (hcl : ∀ y : T, y ≠ genericPoint T → IsClosed ({y} : Set T))
    {c : V.functionField} (hc : c ≠ 0)
    (h : ∀ Γ : Mori.PrimeDivisor V, g Γ.genericPoint = genericPoint T →
      V.ord c Γ.genericPoint = 0) :
    ∃ a : T.functionField, functionFieldMap g a = c := by
  classical
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero hc
  have hfin : {Γ : Mori.PrimeDivisor V | V.ord c Γ.genericPoint ≠ 0}.Finite :=
    (finite_ord_ne_zero φ).subset fun Γ hΓ => by
      simp only [Set.mem_setOf_eq] at hΓ ⊢; rwa [hφ]
  set S := hfin.toFinset
  set Z : Set T := ⋃ Γ ∈ S, {g Γ.genericPoint}
  have hZ : IsClosed Z := by
    refine Set.Finite.isClosed_biUnion S.finite_toSet fun Γ hΓ => hcl _ fun he => ?_
    simp only [S, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hΓ
    exact hΓ (h Γ he)
  set U : T.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have hηU : genericPoint T ∈ U := by
    intro hη
    obtain ⟨Γ, hΓ, hΓη⟩ := Set.mem_iUnion₂.mp hη
    simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hΓ
    exact hΓ (h Γ hΓη.symm)
  have hηV : genericPoint V ∈ g ⁻¹ᵁ U := by
    change g (genericPoint V) ∈ U
    rwa [map_genericPoint_of_isDominant g]
  have : Nonempty (g ⁻¹ᵁ U) := ⟨⟨_, hηV⟩⟩
  have hrange : ∀ x ∈ g ⁻¹ᵁ U, c ∈ (algebraMap (V.presheaf.stalk x) V.functionField).range := by
    intro x hx
    obtain ⟨r, hr⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
      x hc fun Γ hxΓ => by
        by_cases hΓ : V.ord c Γ.genericPoint = 0
        · rw [hΓ]
        · exfalso
          have hΓS : Γ ∈ S := by simp only [S, Set.Finite.mem_toFinset]; exact hΓ
          have hne : g Γ.genericPoint ≠ genericPoint T := fun he => hΓ (h Γ he)
          have hgx : g x = g Γ.genericPoint := by
            rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxΓ
            have h1 := (specializes_iff_mem_closure.mpr hxΓ).map g.continuous
            have h2 := specializes_iff_mem_closure.mp h1
            rwa [(hcl _ hne).closure_eq] at h2
          exact hx (Set.mem_iUnion₂.mpr ⟨Γ, hΓS, hgx⟩)
    exact ⟨r, hr⟩
  obtain ⟨r, hr⟩ := MMP.Intersection.exists_germToFunctionField_eq_of_forall_mem_range_stalk
    (g ⁻¹ᵁ U) hrange
  have := hO U
  obtain ⟨r', rfl⟩ : ∃ r', g.app U r' = r :=
    ⟨(inv (g.app U)).hom r, by
      change (inv (g.app U) ≫ g.app U).hom r = r
      rw [IsIso.inv_hom_id]; rfl⟩
  have hgηU : g (genericPoint V) ∈ U := hηV
  refine ⟨T.presheaf.germ U (genericPoint T) hηU r', ?_⟩
  rw [← hr]
  have h1 := MMP.Mori.functionFieldMap_algebraMap_stalk g (genericPoint V)
    (T.presheaf.germ U (g (genericPoint V)) hgηU r')
  have h2 : algebraMap (T.presheaf.stalk (g (genericPoint V))) T.functionField
      (T.presheaf.germ U (g (genericPoint V)) hgηU r') =
      T.presheaf.germ U (genericPoint T) hηU r' :=
    TopCat.Presheaf.germ_stalkSpecializes_apply T.presheaf hgηU _ r'
  rw [h2] at h1
  rw [h1, Scheme.Hom.germ_stalkMap_apply]
  exact TopCat.Presheaf.germ_stalkSpecializes_apply V.presheaf hηV _ _

end Descent

section PullbackCoeff

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor has coefficient zero along a prime divisor mapping
to the generic point. -/
private theorem coeff_pullback_eq_zero_of_horizontal {V T : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] (g : V ⟶ T) {M : QDivisor T} (hM : M.IsQCartier)
    (hMf : ∀ Z : irreducibleComponents V, g (componentGenericPoint V Z) ∉ M.supp)
    (Γ : Mori.PrimeDivisor V) (hΓ : g Γ.genericPoint = genericPoint T) :
    (M.pullback hM hMf) Γ = 0 := by
  classical
  obtain ⟨D, hD, hDc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hM
  obtain ⟨D', hD', hp⟩ := QDivisor.isPullback_pullback (f := g) hM hMf _
    (QDivisor.cartierIndex_pos hM) D hD hDc
  set U : T.Opens := ⟨(D.supp : Set T)ᶜ, D.isClosed_supp.isOpen_compl⟩
  have h1 : D.IsLocalEquation U 1 := by
    rintro E ⟨x, hxE, hxU⟩
    rw [PrimeDivisor.ord_one]
    by_contra hne
    exact hxU (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hne, hxE⟩)
  have hηU : g Γ.genericPoint ∈ U := by
    change g Γ.genericPoint ∉ (D.supp : Set T)
    rw [hΓ]
    exact MMP.Fourfold.genericPoint_notMem_supp D
  have hΓU : (Γ.support ∩ g ⁻¹ᵁ U).Nonempty := by
    refine ⟨Γ.genericPoint, ?_, hηU⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hc := hp U 1 h1 Γ hΓU
  rw [pullbackComponent_eq _ h1 _ (mem_pointComponent _) 1 (by simp), map_one,
    PrimeDivisor.ordUnit_one] at hc
  have h2 := congrArg (fun G : QDivisor V => G Γ) hD'
  simp only [Finsupp.smul_apply, zsmul_eq_mul] at h2
  have h3 : ((D' Γ : ℤ) : ℚ) = 0 := by
    change ((DivisorWithCoeffs.coeff D' Γ : ℤ) : ℚ) = 0
    rw [hc]; simp
  have hm : ((QDivisor.cartierIndex M hM : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (QDivisor.cartierIndex_pos hM).ne'
  have h4 : (Divisor.toQDivisor D') Γ = ((D' Γ : ℤ) : ℚ) := by
    change DivisorWithCoeffs.coeff (Divisor.toQDivisor D') Γ = _
    rw [Divisor.coeff_toQDivisor]; rfl
  rw [h4, h3] at h2
  push_cast at h2
  exact (mul_eq_zero.mp h2.symm).resolve_left hm

/-- A rational function with nonzero differential exists on an integral scheme of positive
dimension over a perfect field. -/
private theorem exists_D_ne_zero {k : Type} [Field k] [PerfectField k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)} [IsIntegral T] [LocallyOfFiniteType sT] {d : ℕ}
    (hdim : topologicalKrullDim T = d + 1) :
    letI := functionFieldAlgebra sT
    ∃ s : T.functionField, KaehlerDifferential.D k T.functionField s ≠ 0 := by
  let := functionFieldAlgebra sT
  have := essFiniteType_functionField (sX := sT)
  have hK : Module.finrank T.functionField Ω[T.functionField⁄k] = d + 1 :=
    (finrank_kaehlerDifferential_eq_trdeg k T.functionField).trans
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq hdim)
  by_contra h
  push Not at h
  have htop := KaehlerDifferential.span_range_derivation k T.functionField
  have hbot : Submodule.span T.functionField
      (Set.range (KaehlerDifferential.D k T.functionField)) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨s, rfl⟩
    exact h s
  rw [hbot] at htop
  have : Module.finrank T.functionField Ω[T.functionField⁄k] = 0 := by
    rw [← finrank_top, ← htop, finrank_bot]
  omega

/-- Differentials are injective along an isomorphism of algebras. -/
private theorem D_ne_zero_of_algEquiv {k A B : Type*} [Field k] [CommRing A] [CommRing B] [Algebra k A]
    [Algebra k B] (e : A ≃ₐ[k] B) {a : A} (ha : KaehlerDifferential.D k A a ≠ 0) :
    KaehlerDifferential.D k B (e a) ≠ 0 := by
  intro h0
  apply ha
  letI : Algebra B A := e.symm.toRingHom.toAlgebra
  haveI : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq fun c => (e.symm.commutes c).symm
  have := KaehlerDifferential.map_D k k B A (e a)
  rw [h0, map_zero] at this
  have h2 : algebraMap B A (e a) = a := e.symm_apply_apply a
  rw [h2] at this
  exact this.symm

end PullbackCoeff

section CurveCartier

/-- On a normal integral scheme whose prime divisors are closed points, every divisor is
Cartier. -/
private theorem isCartier_of_isClosed_genericPoint {C : Scheme.{0}} [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C]
    (hcl : ∀ P : Mori.PrimeDivisor C, IsClosed ({P.genericPoint} : Set C)) (D : Divisor C) :
    D.IsCartier := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => exact Divisor.isCartier_zero
  | add D D' hD hD' => exact hD.add hD'
  | single P n =>
    rw [← Finsupp.smul_single_one]
    refine Divisor.IsCartier.zsmul ?_ n
    intro x
    by_cases hx : x = P.genericPoint
    · obtain ⟨U, ϖ, φ, hxU, -, -, hφ⟩ :=
        MMP.Fourfold.exists_isLocalEquation_single_of_eq P x hx.symm
      exact ⟨U, hxU, φ, hφ⟩
    · refine ⟨⟨{P.genericPoint}ᶜ, (hcl P).isOpen_compl⟩, hx, 1, ?_⟩
      rintro E' ⟨x', hxE', hxU⟩
      have hE'P : E' ≠ P := by
        rintro rfl
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, (hcl _).closure_eq] at hxE'
        exact hxU hxE'
      rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hE'P), PrimeDivisor.ord_one]

/-- A normal curve is `ℚ`-factorial. -/
private theorem isQFactorial_of_isClosed_genericPoint {k : Type} [Field k] {C : Scheme.{0}}
    {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C]
    (hC : IsNormalVariety k sC)
    (hcl : ∀ P : Mori.PrimeDivisor C, IsClosed ({P.genericPoint} : Set C)) :
    MMP.Fourfold.IsQFactorial sC :=
  ⟨hC, fun D => ⟨1, one_pos, by
    rw [Nat.cast_one, one_smul]; exact isCartier_of_isClosed_genericPoint hcl D⟩⟩

end CurveCartier

section OrdBound

open exteriorPower

/-- Elements of the local ring at a codimension-one point have nonnegative order. -/
private theorem zero_le_ord_algebraMap {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {z : X}
    (hz : Order.coheight z = 1) [IsDiscreteValuationRing (X.presheaf.stalk z)]
    {a : X.presheaf.stalk z} (ha : a ≠ 0) :
    0 ≤ X.ord (algebraMap _ X.functionField a) z := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk z)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hϖ0 : algebraMap (X.presheaf.stalk z) X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  have hu0 : algebraMap (X.presheaf.stalk z) X.functionField u ≠ 0 :=
    (u.isUnit.map _).ne_zero
  have hϖ1 : X.ord (algebraMap _ X.functionField ϖ) z = 1 :=
    (Scheme.ord_eq_iff hz hϖ0).mpr (Ring.ordFrac_irreducible hϖ)
  have hu1 : X.ord (algebraMap _ X.functionField (u : X.presheaf.stalk z)) z = 0 := by
    rw [Scheme.ord_eq_iff hz hu0, ofAdd_zero]
    have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
    exact Ring.ordFrac_of_isUnit u.isUnit
  rw [map_mul, map_pow, Scheme.ord_mul hu0 (pow_ne_zero _ hϖ0), ← zpow_natCast,
    MMP.Mori.ord_zpow z hϖ0, hu1, hϖ1]
  simp

variable {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX]

/-- **Forms with regular coefficients have nonnegative order.** For `a, b ∈ 𝒪_{X,Γ}` on a normal
surface over a perfect field, `ord_Γ(da ∧ db) ≥ 0`. -/
private theorem zero_le_ordForm_formPow_ιMulti (hdim : topologicalKrullDim X = 2)
    (Γ : Mori.PrimeDivisor X) (a b : Γ.localRing) (τ : RationalPluriForms sX 2 ((1 : ℕ) : ℤ))
    (hτ : letI := functionFieldAlgebra sX
      τ = formPow (ιMulti X.functionField 2 (Fin.cons (KaehlerDifferential.D k
        X.functionField (algebraMap Γ.localRing X.functionField a)) fun _ : Fin 1 =>
          KaehlerDifferential.D k X.functionField (algebraMap Γ.localRing X.functionField b))) 1)
    (h0 : τ ≠ 0) : 0 ≤ Γ.ordForm τ := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
    (show topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) by rw [hdim]; rfl)
  obtain ⟨σ, hσ, hσ0⟩ := Γ.exists_topForms_generator hd
  set w := ιMulti Γ.localRing 2 (Fin.cons (KaehlerDifferential.D k Γ.localRing a)
    fun _ : Fin 1 => KaehlerDifferential.D k Γ.localRing b)
  have hw : topFormsMap k Γ.localRing X.functionField 2 w = ιMulti X.functionField 2
      (Fin.cons (KaehlerDifferential.D k X.functionField
        (algebraMap Γ.localRing X.functionField a)) fun _ : Fin 1 =>
          KaehlerDifferential.D k X.functionField (algebraMap Γ.localRing X.functionField b)) := by
    rw [topFormsMap_ιMulti]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [KaehlerDifferential.map_D]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hσ ▸ Submodule.mem_top (x := w))
  rw [Γ.ordForm_eq τ hσ hσ0, hτ, ← hw, ← hc, map_smul,
    algebra_compatible_smul X.functionField c, formPow_smul, pow_one, formCoeff_smul]
  have h1 : formCoeff Γ.localRing hσ hσ0
      (formPow (topFormsMap k Γ.localRing X.functionField 2 σ) 1 : RationalPluriForms sX 2 ((1 : ℕ) : ℤ)) =
      1 := by
    have := repr_smul_formPow (topFormsBasis Γ.localRing hσ hσ0) 1 1
    rwa [one_smul, topFormsBasis_apply] at this
  rw [h1, mul_one]
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply h0
    rw [hτ, ← hw, ← hc, zero_smul, map_zero]
    exact (PiTensorProduct.tprod X.functionField).map_coord_zero (0 : Fin 1) rfl
  have := Γ.isDiscreteValuationRing_localRing
  exact zero_le_ord_algebraMap Γ.coheight_genericPoint hc0

end OrdBound

/-- **The order of a power of a form.** On a normal variety of dimension `d` over a perfect field,
`ord_Γ(c ω^{⊗m}) = ord_Γ(c) + m ord_Γ(ω)` for nonzero `c` and `ω`. -/
private theorem ordForm_smul_formPow {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] {d : ℕ} (hd : topologicalKrullDim X = d) (Γ : Mori.PrimeDivisor X)
    {ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^d Ω[X.functionField⁄k]} (hω : ω ≠ 0)
    {c : X.functionField} (hc : c ≠ 0) (m : ℕ) (τ : RationalPluriForms sX d m)
    (hτ : letI := functionFieldAlgebra sX; τ = c • formPow ω m)
    (τ₁ : RationalPluriForms sX d ((1 : ℕ) : ℤ))
    (hτ₁ : letI := functionFieldAlgebra sX; τ₁ = formPow ω 1) :
    Γ.ordForm τ = X.ord c Γ.genericPoint + m * Γ.ordForm τ₁ := by
  let := functionFieldAlgebra sX
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hd
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hd
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd' b
  set a := b.repr ω ()
  have hωa : ω = a • b () := (basis_unit_repr_smul b ω).symm
  have ha : a ≠ 0 := by
    intro h0; apply hω; rw [hωa, h0, zero_smul]
  have hb0 : ∀ n : ℕ, (formPow (b ()) n : RationalPluriForms sX d n) ≠ 0 := fun n => by
    rw [← ZTensorPower.basis_natCast]; exact (ZTensorPower.basis b n).ne_zero ()
  have e1 : τ = (c * a ^ m) • formPow (b ()) m := by
    rw [hτ, hωa, formPow_smul, smul_smul]
  have e2 : τ₁ = a • formPow (b ()) 1 := by
    rw [hτ₁, hωa, formPow_smul, pow_one]
  have h1 := hN m τ (by
    rw [e1]; exact smul_ne_zero (mul_ne_zero hc (pow_ne_zero _ ha)) (hb0 m))
  have h2 := hN ((1 : ℕ) : ℤ) τ₁ (by rw [e2]; exact smul_ne_zero ha (hb0 1))
  have r1 : (ZTensorPower.basis b m).repr τ () = c * a ^ m := by
    rw [e1, repr_smul_formPow]
  have r2 : (ZTensorPower.basis b ((1 : ℕ) : ℤ)).repr τ₁ () = a := by
    rw [e2, repr_smul_formPow]
  rw [h1, h2, r1, r2, Scheme.ord_mul hc (pow_ne_zero _ ha), ← zpow_natCast,
    MMP.Mori.ord_zpow _ ha]
  push_cast
  ring

/-- **Principal divisors have generic degree zero.** -/
private theorem genericFiberDegree_principalDivisor
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T]
    (hdimV : topologicalKrullDim V = 2) (hQ : IsQFactorial sV)
    (g : V ⟶ T) [IsDominant g] {K : Divisor V} {Δ : QDivisor V}
    (hg : IsMoriFibreSpace sV sT K Δ g) (hdimT : topologicalKrullDim T = 1)
    (φ : (RationalFunctions V)ˣ) :
    MMP.Flips.genericFiberDegree g (Divisor.toQDivisor (principalDivisor φ)) = 0 := by
  obtain ⟨hVv, -⟩ := (Mori.isProjectiveVariety_iff k sV).mp hg.isProjectiveVariety
  have hgc := hg.isContraction
  obtain ⟨hTv, -⟩ := hgc.isNormalVariety_target
  have : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  have hqc : ∀ D : QDivisor V, D.IsQCartier := isQCartier_of_isQFactorial sV hQ
  obtain ⟨U, hU, hUw⟩ := exists_dense_open_genericFiberDegree_eq sV sT hdimV hQ g hg hdimT (Divisor.toQDivisor (principalDivisor φ))
  obtain ⟨w, hwU, hwc⟩ := exists_isClosed_mem_of_isOpen sT U.isOpen hU.nonempty
  obtain ⟨C, -, -, -, hgd⟩ := hUw w hwU hwc
  rw [hgd]
  have hc := Divisor.isCartier_principalDivisor φ
  have : (principalDivisor φ).LinearlyEquivalent 0 := ⟨φ, by rw [sub_zero]⟩
  rw [QDivisor.intersectionNumber_toQDivisor k sV C.ι C.dim_le _ hc,
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sV C.ι C.dim_le hc this,
    Int.cast_zero]

/-- **The horizontal divisor of a log form.** A nonzero rational top form `ω` with
`ord_Γ ω + b_Γ ≥ 0` along every horizontal prime divisor has `ord_Γ ω = -b_Γ` there: the ratio of a
global log pluricanonical form with vertical adjoint divisor by `ω^{⊗m}` has nonpositive order
along every horizontal prime divisor, and generic degree zero. -/
private theorem ordForm_eq_neg_coeff_of_horizontal
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T]
    (hdimV : topologicalKrullDim V = 2) (hQ : IsQFactorial sV)
    (K : Divisor V) (hK : K.IsCanonicalDivisor sV 2)
    (B : QDivisor V) (hlc : MMP.Intersection.IsLogCanonicalPair sV B)
    (ε : ℚ) (hε : 0 < ε ∧ ε < 1)
    (hklt : IsKltPair sV (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))
    (g : V ⟶ T) [IsDominant g]
    (hg : IsMoriFibreSpace sV sT K (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)) g)
    (hdimT : topologicalKrullDim T = 1)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sV g
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)))
    {ω : letI := functionFieldAlgebra sV; ⋀[V.functionField]^2 Ω[V.functionField⁄k]}
    (hω0 : ω ≠ 0) (τ₁ : RationalPluriForms sV 2 ((1 : ℕ) : ℤ))
    (hτ₁ : letI := functionFieldAlgebra sV; τ₁ = formPow ω 1)
    (hω : ∀ Γ : Mori.PrimeDivisor V, g.base Γ.genericPoint = genericPoint T →
      0 ≤ ((Γ.ordForm τ₁ : ℤ) : ℚ) + B Γ)
    (Γ : Mori.PrimeDivisor V) (hΓ : g.base Γ.genericPoint = genericPoint T) :
    ((Γ.ordForm τ₁ : ℤ) : ℚ) = -B Γ := by
  classical
  let := functionFieldAlgebra sV
  obtain ⟨hVv, hVproj⟩ := (Mori.isProjectiveVariety_iff k sV).mp hg.isProjectiveVariety
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have hgc := hg.isContraction
  obtain ⟨hTv, hTn⟩ := hgc.isNormalVariety_target
  have : IsNormal T := hTn
  have : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  have : QuasiCompact sT := hTv.toQuasiCompact
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  obtain ⟨m₁, hm₁, Ω₀, M, hM, hMf, hΩ0, hΩ⟩ := exists_rationalPluriForm_ordForm_add_eq_pullback
    sV sT hdimV hQ K hK B hlc ε hε hklt g hg hdimT hnum
  obtain ⟨b⟩ := exists_basis_topForms (sX := sV) (d := 2) (by rw [hdimV]; norm_cast)
  set a := b.repr ω ()
  have hωa : ω = a • b () := (basis_unit_repr_smul b ω).symm
  have ha : a ≠ 0 := by
    intro h0; apply hω0; rw [hωa, h0, zero_smul]
  set r := (ZTensorPower.basis b m₁).repr Ω₀ ()
  have hΩ₀ : Ω₀ = r • formPow (b ()) m₁ := eq_repr_smul_formPow b Ω₀
  have hr : r ≠ 0 := by
    intro h0; apply hΩ0; rw [hΩ₀, h0, zero_smul] <;> rfl
  set h := r / a ^ m₁
  have hh : h ≠ 0 := div_ne_zero hr (pow_ne_zero _ ha)
  have hΩh : letI := functionFieldAlgebra sV; Ω₀ = h • formPow ω m₁ := by
    rw [hΩ₀, hωa, formPow_smul, smul_smul, div_mul_cancel₀ _ (pow_ne_zero _ ha)]
  -- the order of the ratio along a horizontal prime divisor
  have hordh : ∀ E : Mori.PrimeDivisor V, g.base E.genericPoint = genericPoint T →
      (V.ord h E.genericPoint : ℚ) =
        -(m₁ : ℚ) * (((E.ordForm τ₁ : ℤ) : ℚ) + B E) := by
    intro E hE
    have e1 := hΩ E
    rw [ordForm_smul_formPow (by rw [hdimV]; rfl) E hω0 hh m₁ Ω₀ hΩh τ₁ hτ₁,
      coeff_pullback_eq_zero_of_horizontal g hM hMf E hE] at e1
    push_cast at e1
    linarith
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero hh
  have hdeg := genericFiberDegree_principalDivisor sV sT hdimV hQ g hg hdimT φ
  unfold MMP.Flips.genericFiberDegree at hdeg
  have hcoeff : ∀ E, (Divisor.toQDivisor (principalDivisor φ)).coeff E =
      (V.ord h E.genericPoint : ℚ) := fun E => by
    rw [Divisor.coeff_toQDivisor, coeff_principalDivisor, hφ]
  have hterm : ∀ E ∈ (Divisor.toQDivisor (principalDivisor φ)).support,
      (Divisor.toQDivisor (principalDivisor φ)).coeff E *
        (MMP.Flips.genericFiberPointDegree g E : ℚ) ≤ 0 := by
    intro E _
    by_cases hE : g.base E.genericPoint = genericPoint T
    · rw [hcoeff, hordh E hE]
      have h1 := hω E hE
      have h2 : (0 : ℚ) ≤ MMP.Flips.genericFiberPointDegree g E := by positivity
      have h3 : (0 : ℚ) ≤ m₁ := by positivity
      have h4 : -(m₁ : ℚ) * (((E.ordForm τ₁ : ℤ) : ℚ) + B E) ≤ 0 := by
        rw [neg_mul]; exact neg_nonpos.mpr (mul_nonneg h3 h1)
      exact mul_nonpos_of_nonpos_of_nonneg h4 h2
    · simp [MMP.Flips.genericFiberPointDegree, hE]
  have hall := (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hdeg
  have hzero : V.ord h Γ.genericPoint = 0 := by
    by_cases hmem : Γ ∈ (Divisor.toQDivisor (principalDivisor φ)).support
    · have h1 := hall Γ hmem
      have h2 := one_le_genericFiberPointDegree sV sT hdimV hQ g hg hdimT Γ hΓ
      have h3 : (MMP.Flips.genericFiberPointDegree g Γ : ℚ) ≠ 0 := by
        have : (1 : ℚ) ≤ MMP.Flips.genericFiberPointDegree g Γ := by exact_mod_cast h2
        linarith
      have h4 := (mul_eq_zero.mp h1).resolve_right h3
      rw [hcoeff] at h4
      exact_mod_cast h4
    · have : (Divisor.toQDivisor (principalDivisor φ)).coeff Γ = 0 :=
        Finsupp.notMem_support_iff.mp hmem
      rw [hcoeff] at this
      exact_mod_cast this
  have := hordh Γ hΓ
  rw [hzero] at this
  have hm₁ : (m₁ : ℚ) ≠ 0 := by exact_mod_cast hm₁.ne'
  have : ((Γ.ordForm τ₁ : ℤ) : ℚ) + B Γ = 0 := by
    have h5 : -(m₁ : ℚ) * (((Γ.ordForm τ₁ : ℤ) : ℚ) + B Γ) = 0 := by rw [← this]; simp
    rcases mul_eq_zero.mp h5 with h6 | h6
    · exact absurd (neg_eq_zero.mp h6) hm₁
    · exact h6
  linarith

/-- A finite set of closed points is closed. -/
private theorem isClosed_of_finite_of_forall {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : s.Finite) (h : ∀ y ∈ s, IsClosed ({y} : Set X)) : IsClosed s := by
  rw [← Set.biUnion_of_singleton s]
  exact hs.isClosed_biUnion h

/-- On a surface over a curve with irreducible closed fibres, a prime divisor lying over a closed
point is the whole fibre: two such prime divisors over the same point coincide. -/
private theorem primeDivisor_eq_of_map_genericPoint_eq {V T : Scheme.{0}} [IsIntegral V]
    [IsIntegral T] (g : V ⟶ T)
    (hirr : ∀ t : T, IsClosed ({t} : Set T) → IsIrreducible (g.base ⁻¹' {t}))
    (Γ Γ' : Mori.PrimeDivisor V) {t : T} (ht : IsClosed ({t} : Set T))
    (hΓ : g Γ.genericPoint = t) (hΓ' : g Γ'.genericPoint = t)
    (htη : t ≠ genericPoint T) (hdom : g (genericPoint V) = genericPoint T) : Γ = Γ' := by
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (hirr t ht) (ht.preimage g.continuous)
  have key : ∀ E : Mori.PrimeDivisor V, g E.genericPoint = t → E.genericPoint = ξ := by
    intro E hE
    have hmem : E.genericPoint ∈ closure ({ξ} : Set V) := by rw [hξ.def]; exact hE
    have hle : E.genericPoint ≤ ξ := specializes_iff_mem_closure.mpr hmem
    by_contra hne
    have hlt : E.genericPoint < ξ := lt_of_le_not_ge hle fun h =>
      hne (inseparable_iff_specializes_and.mpr ⟨h, hle⟩).eq
    have hξη : ξ ≠ genericPoint V := by
      intro h
      apply htη
      have hgξ : g ξ = t := hξ.mem
      rw [← hgξ, h, hdom]
    have hξle : ξ ≤ genericPoint V := (genericPoint_spec V).specializes trivial
    have hlt2 : ξ < genericPoint V := lt_of_le_not_ge hξle fun h =>
      hξη (inseparable_iff_specializes_and.mpr ⟨h, hξle⟩).eq
    have h1 := Order.coheight_add_one_le hlt
    have h2 := Order.coheight_add_one_le hlt2
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E] at h1
    have h3 : (1 : ℕ∞) ≤ Order.coheight ξ := le_trans le_add_self h2
    have : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add h3 le_rfl) h1
    norm_num at this
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective ((key Γ hΓ).trans (key Γ' hΓ').symm)

/-- A nonzero rational function on a normal curve is a unit at all but finitely many points. -/
private theorem finite_setOf_ord_ne_zero {T : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] [CompactSpace T] {a : T.functionField} (ha : a ≠ 0) :
    {y : T | T.ord a y ≠ 0}.Finite := by
  classical
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero ha
  refine ((finite_ord_ne_zero φ).image Mori.PrimeDivisor.genericPoint).subset fun y hy => ?_
  have hy1 : Order.coheight y = 1 := by
    by_contra h
    exact hy (Scheme.ord_eq_zero_of_coheight_neq_one h a)
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy1, ?_,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _⟩
  change Mori.PrimeDivisor.ord _ φ ≠ 0
  have e : Mori.PrimeDivisor.genericPoint (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy1) =
      y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  rw [hφ, e]
  exact hy

/-- A rational function of order zero at a codimension-one point of a normal scheme is a unit
of the local ring there. -/
private theorem exists_isUnit_algebraMap_eq_of_ord_eq_zero {T : Scheme.{0}} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] {y : T} (hy : Order.coheight y = 1)
    {a : T.functionField} (ha : a ≠ 0) (h0 : T.ord a y = 0) :
    ∃ u : T.presheaf.stalk y, IsUnit u ∧ algebraMap _ T.functionField u = a := by
  set P : Mori.PrimeDivisor T := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy
  have hP : P.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have := P.isDiscreteValuationRing_localRing
  have hmem : ∀ b : T.functionField, b ≠ 0 → T.ord b y = 0 →
      ∃ r : T.presheaf.stalk y, algebraMap _ T.functionField r = b := by
    intro b hb hb0
    obtain ⟨r, hr⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
      y hb fun Γ hΓ => by
        by_cases hΓy : Γ.genericPoint = y
        · rw [hΓy, hb0]
        · exfalso
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hΓ
          have hle : y ≤ Γ.genericPoint := specializes_iff_mem_closure.mpr hΓ
          have hlt : y < Γ.genericPoint := lt_of_le_not_ge hle fun h =>
            hΓy (inseparable_iff_specializes_and.mpr ⟨h, hle⟩).eq.symm
          have h1 := Order.coheight_add_one_le hlt
          rw [hy, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h1
          norm_num at h1
    exact ⟨r, hr⟩
  obtain ⟨r, hr⟩ := hmem a ha h0
  obtain ⟨r', hr'⟩ := hmem a⁻¹ (inv_ne_zero ha) (by
    rw [show a⁻¹ = a ^ (-1 : ℤ) from (zpow_neg_one a).symm, MMP.Mori.ord_zpow y ha, h0, mul_zero])
  refine ⟨r, IsUnit.of_mul_eq_one r' ?_, hr⟩
  apply IsFractionRing.injective (T.presheaf.stalk y) T.functionField
  rw [map_mul, hr, hr', mul_inv_cancel₀ ha, map_one]

/-- The pull-back of a rational function along a dominant morphism, at a prime divisor over a
point where the function is a unit, has order zero. -/
private theorem ord_functionFieldMap_eq_zero_of_isUnit {V T : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsIntegral T] (g : V ⟶ T) [IsDominant g] (Γ : Mori.PrimeDivisor V)
    {u : T.presheaf.stalk (g Γ.genericPoint)} (hu : IsUnit u) :
    V.ord (functionFieldMap g (algebraMap _ T.functionField u)) Γ.genericPoint = 0 := by
  rw [MMP.Mori.functionFieldMap_algebraMap_stalk g Γ.genericPoint u]
  exact Γ.ord_algebraMap_of_isUnit (hu.map _)

/-- At a codimension-one point of a normal locally Noetherian integral scheme there is a rational
function of order one, the image of an element of the maximal ideal of the stalk. -/
private theorem exists_ord_eq_one {T : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] {y : T} (hy : Order.coheight y = 1) :
    ∃ p : T.presheaf.stalk y, ¬ IsUnit p ∧ T.ord (algebraMap _ T.functionField p) y = 1 := by
  set P : Mori.PrimeDivisor T := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy
  have hP : P.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hdvr : IsDiscreteValuationRing (T.presheaf.stalk y) :=
    hP ▸ P.isDiscreteValuationRing_localRing
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (T.presheaf.stalk y)
  have hp0 : algebraMap (T.presheaf.stalk y) T.functionField p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hp.ne_zero
  exact ⟨p, hp.not_isUnit, (Scheme.ord_eq_iff hy hp0).mpr (Ring.ordFrac_irreducible hp)⟩

/-- **Local generators of a vertical `ℚ`-divisor.** Let `g : V ⟶ T` be a dominant morphism of a
normal surface onto a normal curve with irreducible closed fibres, and `E` a `ℚ`-divisor on `V`
vanishing along every horizontal prime divisor. For some even `m₀ > 0`, every point `t ∈ T` has
an open neighbourhood `W_t` and a rational function `ψ_t` on `T`, `ψ_t = 1` for all but finitely
many `t` and of order zero at every point of `W_t` other than `t`, such that `g^*ψ_t` has order
`-m₀ E` along every prime divisor meeting `g⁻¹ W_t`. -/
private theorem exists_localGenerator_of_vertical {V T : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [CompactSpace T] (g : V ⟶ T) [IsDominant g] (hdimT : topologicalKrullDim T = 1)
    (hcl : ∀ y : T, y ≠ genericPoint T → IsClosed ({y} : Set T))
    (hirr : ∀ t : T, IsClosed ({t} : Set T) → IsIrreducible (g.base ⁻¹' {t}))
    (E : QDivisor V) (hE : ∀ Γ : Mori.PrimeDivisor V, g Γ.genericPoint = genericPoint T → E Γ = 0) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ Even m₀ ∧ ∃ ψ : T → T.functionField, (∀ t, ψ t ≠ 0) ∧
      {t | ψ t ≠ 1}.Finite ∧ ∃ W : T → T.Opens, (∀ t, t ∈ W t) ∧
      (∀ t (Γ : Mori.PrimeDivisor V), (Γ.support ∩ g ⁻¹ᵁ W t).Nonempty →
        (V.ord (functionFieldMap g (ψ t)) Γ.genericPoint : ℚ) + m₀ * E Γ = 0) ∧
      (∀ t y, y ∈ W t → y ≠ t → T.ord (ψ t) y = 0) ∧
      (∀ t y, y ∈ W t → y ≠ t → ψ y = 1) := by
  classical
  have hdomη : g (genericPoint V) = genericPoint T := map_genericPoint_of_isDominant g
  set S := E.support
  have hSv : ∀ Γ ∈ S, g Γ.genericPoint ≠ genericPoint T := fun Γ hΓ he =>
    (Finsupp.mem_support_iff.mp hΓ) (hE Γ he)
  -- a uniformizer below each vertical prime divisor of the support
  have hunif : ∀ Γ : Mori.PrimeDivisor V, ∃ p : T.presheaf.stalk (g Γ.genericPoint),
      Γ ∈ S → ¬ IsUnit p ∧ T.ord (algebraMap _ T.functionField p) (g Γ.genericPoint) = 1 := by
    intro Γ
    by_cases hΓ : Γ ∈ S
    · obtain ⟨p, hp, hp1⟩ := exists_ord_eq_one
        (MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hdimT (hSv Γ hΓ))
      exact ⟨p, fun _ => ⟨hp, hp1⟩⟩
    · exact ⟨0, fun h => absurd h hΓ⟩
  choose p hp using hunif
  set ϖ : Mori.PrimeDivisor V → T.functionField := fun Γ => algebraMap _ T.functionField (p Γ)
  have hϖ0 : ∀ Γ ∈ S, ϖ Γ ≠ 0 := fun Γ hΓ h0 => by
    have := (hp Γ hΓ).2; rw [show algebraMap _ T.functionField (p Γ) = 0 from h0] at this
    simp at this
  -- the multiplicity of the fibre
  set μ : Mori.PrimeDivisor V → ℤ := fun Γ => V.ord (functionFieldMap g (ϖ Γ)) Γ.genericPoint
  have hμ : ∀ Γ ∈ S, μ Γ ≠ 0 := by
    intro Γ hΓ h0
    have hne : functionFieldMap g (ϖ Γ) ≠ 0 := (map_ne_zero _).mpr (hϖ0 Γ hΓ)
    obtain ⟨u, hu, hue⟩ := exists_isUnit_algebraMap_eq_of_ord_eq_zero
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Γ) hne h0
    simp only [ϖ] at hue
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk g Γ.genericPoint (p Γ)] at hue
    have h1 := IsFractionRing.injective (V.presheaf.stalk Γ.genericPoint) V.functionField hue
    rw [h1] at hu
    exact (hp Γ hΓ).1 ((isUnit_map_iff (g.stalkMap Γ.genericPoint).hom _).mp hu)
  -- the integer `m₀`
  set m₀ : ℕ := 2 * ∏ Γ ∈ S, ((μ Γ).natAbs * (E Γ).den)
  have hm₀ : 0 < m₀ := by
    refine Nat.mul_pos two_pos (Finset.prod_pos fun Γ hΓ => Nat.mul_pos ?_ (E Γ).den_pos)
    exact Int.natAbs_pos.mpr (hμ Γ hΓ)
  have hN : ∀ Γ ∈ S, ∃ N : ℤ, (N : ℚ) * μ Γ = -((m₀ : ℚ) * E Γ) := by
    intro Γ hΓ
    obtain ⟨c, hc⟩ : (μ Γ).natAbs * (E Γ).den ∣ m₀ :=
      Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hΓ) 2
    have key : (E Γ : ℚ) * (E Γ).den = (E Γ).num := Rat.mul_den_eq_num _
    have hm : (m₀ : ℚ) * E Γ = |((μ Γ : ℤ) : ℚ)| * c * (E Γ).num := by
      rw [hc]; push_cast; rw [← key, Nat.cast_natAbs, Int.cast_abs]; ring
    rcases le_total 0 (μ Γ) with h | h
    · refine ⟨-(c * (E Γ).num), ?_⟩
      rw [hm, abs_of_nonneg (by exact_mod_cast h)]
      push_cast; ring
    · refine ⟨c * (E Γ).num, ?_⟩
      rw [hm, abs_of_nonpos (by exact_mod_cast h)]
      push_cast; ring
  choose! N hNspec using hN
  -- the functions `ψ_t`
  set ψ : T → T.functionField := fun t =>
    if h : ∃ Γ ∈ S, g Γ.genericPoint = t then ϖ h.choose ^ N h.choose else 1
  have hψ0 : ∀ t, ψ t ≠ 0 := by
    intro t
    simp only [ψ]
    split_ifs with h
    · exact zpow_ne_zero _ (hϖ0 _ h.choose_spec.1)
    · exact one_ne_zero
  have hψ1 : {t | ψ t ≠ 1} ⊆ (fun Γ : Mori.PrimeDivisor V => g Γ.genericPoint) '' (↑S : Set (Mori.PrimeDivisor V)) := by
    intro t ht
    by_contra hcon
    apply ht
    simp only [ψ]
    rw [dif_neg]
    rintro ⟨Γ, hΓ, rfl⟩
    exact hcon ⟨Γ, hΓ, rfl⟩
  have hψfin : {t | ψ t ≠ 1}.Finite := (S.finite_toSet.image _).subset hψ1
  -- the opens `W_t`
  have hZfin : ∀ t, ((fun Γ : Mori.PrimeDivisor V => g Γ.genericPoint) '' (↑S : Set (Mori.PrimeDivisor V)) ∪
      {y : T | T.ord (ψ t) y ≠ 0}).Finite := fun t =>
    (S.finite_toSet.image _).union (finite_setOf_ord_ne_zero (hψ0 t))
  have hZη : ∀ t, genericPoint T ∉ ((fun Γ : Mori.PrimeDivisor V => g Γ.genericPoint) '' (↑S : Set (Mori.PrimeDivisor V)) ∪
      {y : T | T.ord (ψ t) y ≠ 0}) := by
    intro t h
    rcases h with ⟨Γ, hΓ, he⟩ | h
    · exact hSv Γ hΓ he
    · apply h
      refine Scheme.ord_eq_zero_of_coheight_neq_one ?_ _
      rw [Order.coheight_eq_zero.mpr ?_]
      · simp
      · intro y _
        exact (genericPoint_spec T).specializes trivial
  have hZcl : ∀ t, IsClosed (((fun Γ : Mori.PrimeDivisor V => g Γ.genericPoint) '' (↑S : Set (Mori.PrimeDivisor V)) ∪
      {y : T | T.ord (ψ t) y ≠ 0}) \ {t}) := fun t =>
    isClosed_of_finite_of_forall (hZfin t).diff (fun y hy => hcl y fun h => hZη t (h ▸ hy.1))
  set W : T → T.Opens := fun t => ⟨_, (hZcl t).isOpen_compl⟩
  refine ⟨m₀, hm₀, ⟨∏ Γ ∈ S, ((μ Γ).natAbs * (E Γ).den), by ring⟩, ψ, hψ0, hψfin, W,
    fun t ht => ht.2 rfl, ?_, ?_, ?_⟩
  · intro t Γ ⟨x, hxΓ, hxW⟩
    by_cases hΓh : g Γ.genericPoint = genericPoint T
    · rw [hE Γ hΓh, mul_zero, add_zero]
      exact_mod_cast ord_functionFieldMap_eq_zero g Γ hΓh (hψ0 t)
    · -- `Γ` lies over the closed point `t'' = g(η_Γ)`
      set t'' := g Γ.genericPoint
      have hgx : g x = t'' := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxΓ
        have h1 := (specializes_iff_mem_closure.mpr hxΓ).map g.continuous
        have h2 := specializes_iff_mem_closure.mp h1
        rwa [(hcl _ hΓh).closure_eq] at h2
      have ht''W : t'' ∈ W t := hgx ▸ hxW
      by_cases ht'' : t'' = t
      · by_cases hΓS : Γ ∈ S
        · have hex : ∃ Γ' ∈ S, g Γ'.genericPoint = t := ⟨Γ, hΓS, ht''⟩
          have hch : hex.choose = Γ :=
            primeDivisor_eq_of_map_genericPoint_eq g hirr _ _ (ht'' ▸ hcl _ hΓh)
              hex.choose_spec.2 ht'' (ht'' ▸ hΓh) hdomη
          have hψt : ψ t = ϖ Γ ^ N Γ := by
            simp only [ψ, dif_pos hex, hch]
          rw [hψt, map_zpow₀, MMP.Mori.ord_zpow _ ((map_ne_zero _).mpr (hϖ0 Γ hΓS))]
          push_cast
          rw [hNspec Γ hΓS]
          ring
        · have hE0 : E Γ = 0 := by simpa [S] using hΓS
          rw [hE0, mul_zero, add_zero]
          by_cases hex : ∃ Γ' ∈ S, g Γ'.genericPoint = t
          · exfalso
            have := primeDivisor_eq_of_map_genericPoint_eq g hirr _ _ (ht'' ▸ hcl _ hΓh)
              hex.choose_spec.2 ht'' (ht'' ▸ hΓh) hdomη
            exact hΓS (this ▸ hex.choose_spec.1)
          · have hψt : ψ t = 1 := by simp only [ψ, dif_neg hex]
            rw [hψt, map_one]
            simp
      · -- `t'' ≠ t`, so `t''` lies outside the support and `ψ_t` is a unit at `t''`
        have hnot : t'' ∉ ((fun Γ : Mori.PrimeDivisor V => g Γ.genericPoint) '' (↑S : Set (Mori.PrimeDivisor V)) ∪
            {y : T | T.ord (ψ t) y ≠ 0}) := fun h => ht''W ⟨h, ht''⟩
        have hΓS : Γ ∉ S := fun h => hnot (Or.inl ⟨Γ, h, rfl⟩)
        have hE0 : E Γ = 0 := by simpa [S] using hΓS
        have hord0 : T.ord (ψ t) t'' = 0 := by
          by_contra h; exact hnot (Or.inr h)
        obtain ⟨u, hu, hue⟩ := exists_isUnit_algebraMap_eq_of_ord_eq_zero
          (MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hdimT hΓh) (hψ0 t) hord0
        rw [hE0, mul_zero, add_zero, ← hue]
        exact_mod_cast ord_functionFieldMap_eq_zero_of_isUnit g Γ hu
  · intro t y hy hyt
    by_contra h
    exact hy ⟨Or.inr h, hyt⟩
  · intro t y hy hyt
    by_contra h
    exact hy ⟨Or.inl (hψ1 h), hyt⟩

/-- A finite map onto a prime divisor sends the generic point to the generic point. -/
private theorem map_genericPoint_eq_of_range_eq {V N : Scheme.{0}} [IsIntegral N] (ν : N ⟶ V)
    (P : Mori.PrimeDivisor V) (hrange : Set.range ν.base = (P.support : Set V)) :
    ν (genericPoint N) = P.genericPoint := by
  have hP' : P.genericPoint ∈ Set.range ν.base := by
    rw [hrange, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  obtain ⟨x, hx⟩ := hP'
  have h1 : ν (genericPoint N) ⤳ P.genericPoint := by
    rw [← hx]; exact ((genericPoint_spec N).specializes trivial).map ν.continuous
  have h2 : P.genericPoint ⤳ ν (genericPoint N) := by
    have : ν (genericPoint N) ∈ (P.support : Set V) := hrange ▸ ⟨_, rfl⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
    exact specializes_iff_mem_closure.mpr this
  exact (inseparable_iff_specializes_and.mpr ⟨h1, h2⟩).eq

/-- The pull-back of a rational function on the base is regular at the generic point of a curve
`N ⟶ V` mapping onto the base, with restriction the pull-back along `N ⟶ T`. -/
private theorem exists_stalk_eq_functionFieldMap {V T N : Scheme.{0}} [IsIntegral V]
    [IsIntegral T] [IsIntegral N] (g : V ⟶ T) (ν : N ⟶ V) [IsDominant g] [IsDominant (ν ≫ g)]
    (hgη : g (ν (genericPoint N)) = genericPoint T) (a : T.functionField) :
    ∃ c : V.presheaf.stalk (ν (genericPoint N)),
      algebraMap _ V.functionField c = functionFieldMap g a ∧
        (ν.stalkMap (genericPoint N)).hom c = functionFieldMap (ν ≫ g) a := by
  set a' : T.presheaf.stalk (g (ν (genericPoint N))) :=
    (T.presheaf.stalkSpecializes (show g (ν (genericPoint N)) ⤳ genericPoint T by
      rw [hgη])).hom a
  have ha' : algebraMap (T.presheaf.stalk (g (ν (genericPoint N)))) T.functionField a' = a := by
    change (T.presheaf.stalkSpecializes _ ≫ T.presheaf.stalkSpecializes _).hom a = a
    rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  refine ⟨(g.stalkMap (ν (genericPoint N))).hom a', ?_, ?_⟩
  · rw [← MMP.Mori.functionFieldMap_algebraMap_stalk g (ν (genericPoint N)) a', ha']
  · have e1 : ((ν ≫ g).stalkMap (genericPoint N)).hom a' =
        (ν.stalkMap (genericPoint N)).hom ((g.stalkMap (ν (genericPoint N))).hom a') := by
      rw [Scheme.Hom.stalkMap_comp]; rfl
    rw [← e1]
    rfl

/-- **Pull-back of `b (dy)^{⊗m}` on a curve.** -/
private theorem pluriformPullback_smul_formPow_D {k : Type} [Field k] [CharZero k]
    {X X' : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k)) [IsIntegral X]
    [IsIntegral X'] [LocallyOfFiniteType sX] [LocallyOfFiniteType sX']
    (hX : topologicalKrullDim X = 1) (hX' : topologicalKrullDim X' = 1)
    (φ : FunctionFieldHom sX sX') (y b : X'.functionField)
    (hy : letI := functionFieldAlgebra sX'; KaehlerDifferential.D k X'.functionField y ≠ 0)
    (m : ℕ) :
    letI := functionFieldAlgebra sX'
    letI := functionFieldAlgebra sX
    pluriformPullback sX sX' φ 1 m (b • formPow (exteriorPower.ιMulti X'.functionField 1
        fun _ : Fin 1 => KaehlerDifferential.D k X'.functionField y) m) =
      φ b • formPow (exteriorPower.ιMulti X.functionField 1
        fun _ : Fin 1 => KaehlerDifferential.D k X.functionField (φ y)) m := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  obtain ⟨b'⟩ := exists_basis_topForms (sX := sX') (d := 1) (by rw [hX']; rfl)
  have hline : Module.finrank X'.functionField
      (⋀[X'.functionField]^1 Ω[X'.functionField⁄k]) = 1 := by
    rw [Module.finrank_eq_card_basis b', Fintype.card_unit]
  set w := exteriorPower.ιMulti X'.functionField 1
    fun _ : Fin 1 => KaehlerDifferential.D k X'.functionField y
  have hw0 : w ≠ 0 := by
    intro h0
    apply hy
    have := congrArg (exteriorPower.oneEquiv X'.functionField _) h0
    simp only [w, exteriorPower.oneEquiv_ιMulti, map_zero] at this
    exact this
  have hspan : Submodule.span X'.functionField {w} = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' w hw0).mp hline v
    exact Submodule.mem_span_singleton.mpr ⟨c, hc⟩
  have hgen := isPullbackGenerator_functionFieldHom (sX := sX) (sX' := sX') (d := 1)
    (by rw [hX]; rfl) (by rw [hX']; rfl) φ hspan hw0
  rw [pluriformPullback_smul_formPow φ hgen m b]
  congr 2
  rw [topFormsMap_ιMulti]
  congr 1
  funext i
  rw [KaehlerDifferential.map_D]
  rfl

/-- A one-fold exterior product of a nonzero vector is nonzero. -/
private theorem ιMulti_fin_one_ne_zero {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {v : M} (hv : v ≠ 0) : exteriorPower.ιMulti R 1 (fun _ : Fin 1 => v) ≠ 0 := by
  intro h0
  apply hv
  have := congrArg (exteriorPower.oneEquiv R M) h0
  simpa [exteriorPower.oneEquiv_ιMulti] using this

/-- A tensor power of a nonzero top form on a variety is nonzero. -/
private theorem formPow_ne_zero_of_ne_zero {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = d)
    {ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^d Ω[X.functionField⁄k]} (hω : ω ≠ 0)
    (m : ℕ) : letI := functionFieldAlgebra sX; (formPow ω m : RationalPluriForms sX d m) ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hd
  set a := b.repr ω ()
  have hωa : ω = a • b () := (basis_unit_repr_smul b ω).symm
  have ha : a ≠ 0 := by
    intro h0; apply hω; rw [hωa, h0, zero_smul]
  rw [hωa, formPow_smul, ← ZTensorPower.basis_natCast]
  exact smul_ne_zero (pow_ne_zero _ ha) ((ZTensorPower.basis b m).ne_zero ())

/-- The extension of function fields of a dominant morphism of varieties, as a `k`-homomorphism. -/
private noncomputable def functionFieldHomOf {k : Type} [Field k] {X Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] : FunctionFieldHom (f ≫ sY) sY :=
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (f ≫ sY)
  letI := functionFieldMapAlgebra f
  haveI := isScalarTower_functionFieldMap sY f
  { functionFieldMap f with
    commutes' := fun c => (IsScalarTower.algebraMap_apply k Y.functionField X.functionField c).symm }

/-- **Orders of forms are invariant under isomorphisms.** -/
private theorem ordForm_pluriformPullback_of_isIso {k : Type} [Field k] [PerfectField k]
    {N₁ N₂ : Scheme.{0}} {s₁ : N₁ ⟶ Spec (.of k)} {s₂ : N₂ ⟶ Spec (.of k)}
    [IsIntegral N₁] [IsLocallyNoetherian N₁] [IsNormal N₁] [IsIntegral N₂]
    [IsLocallyNoetherian N₂] [IsNormal N₂] [LocallyOfFiniteType s₂] (α : N₁ ⟶ N₂) [IsIso α]
    (hα : α ≫ s₂ = s₁) {d : ℕ} (hd : topologicalKrullDim N₂ = d) (φ : FunctionFieldHom s₁ s₂)
    (hφ : letI := functionFieldAlgebra s₁; letI := functionFieldAlgebra s₂
      ∀ a, φ a = functionFieldMap α a)
    (Q₁ : Mori.PrimeDivisor N₁) (Q₂ : Mori.PrimeDivisor N₂) (hQ : α Q₁.genericPoint = Q₂.genericPoint)
    {m : ℤ} (τ : RationalPluriForms s₂ d m) :
    Q₁.ordForm (pluriformPullback s₁ s₂ φ d m τ) = Q₂.ordForm τ := by
  subst hα
  have hφ' : φ = functionFieldHomOf s₂ α := by
    let := functionFieldAlgebra s₂
    let := functionFieldAlgebra (α ≫ s₂)
    exact AlgHom.ext fun a => hφ a
  subst hφ'
  have hbij : Function.Bijective (functionFieldMap α) :=
    MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion α ⊤ (by simp)
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := s₂) hd
  exact MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso α hbij hd' Q₁ Q₂ hQ τ

/-- **A form whose twist generates the boundary is a pulled-back multiple of a log form.** Let
`ω₀` be a top form with `ord_Γ ω₀ = -b_Γ` along every horizontal prime divisor. If `g^*φ · Ω`
generates `𝒪(m(K + B))` over `g⁻¹ U` for an open `U` containing the generic point, then
`Ω = g^*a · ω₀^{⊗m}` for a rational function `a` on the base. -/
private theorem exists_eq_functionFieldMap_smul_formPow {k : Type} [Field k] [PerfectField k]
    {V T : Scheme.{0}} {sV : V ⟶ Spec (.of k)} [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] [LocallyOfFiniteType sV] [IsIntegral T]
    (hdimV : topologicalKrullDim V = 2) (g : V ⟶ T) [IsDominant g]
    (hO : ∀ U : T.Opens, IsIso (g.app U))
    (hcl : ∀ y : T, y ≠ genericPoint T → IsClosed ({y} : Set T)) (B : QDivisor V)
    {ω₀ : letI := functionFieldAlgebra sV; ⋀[V.functionField]^2 Ω[V.functionField⁄k]}
    (hω0 : ω₀ ≠ 0) (τ₁ : RationalPluriForms sV 2 ((1 : ℕ) : ℤ))
    (hτ₁ : letI := functionFieldAlgebra sV; τ₁ = formPow ω₀ 1)
    (hhor : ∀ Γ : Mori.PrimeDivisor V, g Γ.genericPoint = genericPoint T →
      ((Γ.ordForm τ₁ : ℤ) : ℚ) + B Γ = 0)
    {m : ℕ} (Ω : RationalPluriForms sV 2 m) (U : T.Opens) (hηU : genericPoint T ∈ U)
    (φ : T.functionField) (hU : GeneratesOn B m (g ⁻¹ᵁ U) (functionFieldMap g φ • Ω)) :
    ∃ a : T.functionField, a ≠ 0 ∧
      letI := functionFieldAlgebra sV
      Ω = (functionFieldMap g a • formPow ω₀ m : RationalPluriForms sV 2 m) := by
  let := functionFieldAlgebra sV
  obtain ⟨b⟩ := exists_basis_topForms (sX := sV) (d := 2) (by rw [hdimV]; norm_cast)
  set c₀ := b.repr ω₀ ()
  have hωa : ω₀ = c₀ • b () := (basis_unit_repr_smul b ω₀).symm
  have hc₀ : c₀ ≠ 0 := by
    intro h0; apply hω0; rw [hωa, h0, zero_smul]
  have hΩ0 : Ω ≠ 0 := fun h => hU.1 (by rw [h, smul_zero])
  have hφ0 : φ ≠ 0 := fun h => hU.1 (by rw [h, map_zero, zero_smul])
  set r := (ZTensorPower.basis b m).repr Ω ()
  have hΩr : Ω = r • formPow (b ()) m := eq_repr_smul_formPow b Ω
  have hr : r ≠ 0 := by
    intro h0; apply hΩ0; rw [hΩr, h0, zero_smul] <;> rfl
  set c := r / c₀ ^ m
  have hc : c ≠ 0 := div_ne_zero hr (pow_ne_zero _ hc₀)
  have hΩc : Ω = c • formPow ω₀ m := by
    rw [hΩr, hωa, formPow_smul, smul_smul, div_mul_cancel₀ _ (pow_ne_zero _ hc₀)]
  have hφ' : functionFieldMap g φ ≠ 0 := (map_ne_zero _).mpr hφ0
  -- the order of `c` along horizontal prime divisors vanishes
  have hord : ∀ Γ : Mori.PrimeDivisor V, g Γ.genericPoint = genericPoint T →
      V.ord c Γ.genericPoint = 0 := by
    intro Γ hΓ
    have hmeet : (Γ.support ∩ g ⁻¹ᵁ U).Nonempty := by
      refine ⟨Γ.genericPoint, ?_, ?_⟩
      · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      · change g Γ.genericPoint ∈ U; rw [hΓ]; exact hηU
    have e1 := hU.2 Γ hmeet
    have e2 := ordForm_smul_formPow hdimV Γ hω0 (mul_ne_zero hφ' hc) m
      (functionFieldMap g φ • Ω) (by rw [hΩc]; exact smul_smul _ _ _) τ₁ hτ₁
    rw [e2, Scheme.ord_mul hφ' hc, ord_functionFieldMap_eq_zero g Γ hΓ hφ0, zero_add] at e1
    have e3 := hhor Γ hΓ
    rw [show B.coeff Γ = B Γ from rfl] at e1
    have : ((V.ord c Γ.genericPoint : ℤ) : ℚ) = 0 := by
      push_cast at e1 ⊢; linear_combination e1 - (m : ℚ) * e3
    exact_mod_cast this
  obtain ⟨a, ha⟩ := exists_functionFieldMap_eq_of_forall_ord_eq_zero g hO hcl hc hord
  refine ⟨a, fun h0 => hc (by rw [← ha, h0, map_zero]), ?_⟩
  rw [hΩc, ha]

/-- **One branch of the horizontal floor.** Let `ν : N ⟶ V` be a closed immersion of a normal
curve onto a horizontal prime divisor `P` with `ν ≫ g` an isomorphism, `f` a rational function of
order `ε n` along `P`, and `ω₀ = n⁻¹ f⁻¹ df ∧ g^* ds`. Then residues of `g^*a · ω₀^{⊗m}` along
`ν` are `(ν ≫ g)^*a · ε^m (d(ν ≫ g)^*s)^{⊗m}`, and the boundary `Θ` read off from the residues of
the local generators `g^*ψ_t · ω₀^{⊗m₀}` is an adjunction boundary. -/
private theorem exists_adjunctionBoundary_of_section
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [LocallyOfFiniteType sV]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [LocallyOfFiniteType sT]
    (hdimV : topologicalKrullDim V = 2) (hdimT : topologicalKrullDim T = 1)
    (g : V ⟶ T) [IsDominant g] (B : QDivisor V)
    {f : V.functionField} (hf : f ≠ 0) {n : ℕ} (hn : 0 < n) (s : T.functionField)
    (ω₀ : letI := functionFieldAlgebra sV; ⋀[V.functionField]^2 Ω[V.functionField⁄k])
    (hω₀ : letI := functionFieldAlgebra sV
      ω₀ = (algebraMap k V.functionField (n : k)⁻¹ * f⁻¹) • exteriorPower.ιMulti V.functionField 2
        (Fin.cons (KaehlerDifferential.D k V.functionField f) fun _ : Fin 1 =>
          KaehlerDifferential.D k V.functionField (functionFieldMap g s)))
    (hω0 : ω₀ ≠ 0) (τ₁ : RationalPluriForms sV 2 ((1 : ℕ) : ℤ))
    (hτ₁ : letI := functionFieldAlgebra sV; τ₁ = formPow ω₀ 1)
    (m₀ : ℕ) (hm₀ : 0 < m₀) (hm₀e : Even m₀) (ψ : T → T.functionField) (hψ0 : ∀ t, ψ t ≠ 0)
    (hψfin : {t | ψ t ≠ 1}.Finite) (W : T → T.Opens) (hW : ∀ t, t ∈ W t)
    (hgen : ∀ t (Γ : Mori.PrimeDivisor V), (Γ.support ∩ g ⁻¹ᵁ W t).Nonempty →
      (V.ord (functionFieldMap g (ψ t)) Γ.genericPoint : ℚ) +
        m₀ * (((Γ.ordForm τ₁ : ℤ) : ℚ) + B Γ) = 0)
    (hWord : ∀ t y, y ∈ W t → y ≠ t → T.ord (ψ t) y = 0)
    (hWψ : ∀ t y, y ∈ W t → y ≠ t → ψ y = 1)
    (P : Mori.PrimeDivisor V) (hPh : g P.genericPoint = genericPoint T)
    (N : Scheme.{0}) [IsIntegral N] [IsLocallyNoetherian N] [IsNormal N] (ν : N ⟶ V)
    [IsDominant (ν ≫ g)] [IsClosedImmersion ν] [IsIso (ν ≫ g)]
    (hνη : ν (genericPoint N) = P.genericPoint) (ε : ℤ) (hε : V.ord f P.genericPoint = ε * n)
    (hε1 : ε ^ 2 = 1)
    (hs : letI := functionFieldAlgebra (ν ≫ sV)
      KaehlerDifferential.D k N.functionField (functionFieldMap (ν ≫ g) s) ≠ 0)
    (τN : RationalPluriForms (ν ≫ sV) 1 ((1 : ℕ) : ℤ))
    (hτN : letI := functionFieldAlgebra (ν ≫ sV)
      τN = formPow (exteriorPower.ιMulti N.functionField 1 fun _ : Fin 1 =>
        KaehlerDifferential.D k N.functionField (functionFieldMap (ν ≫ g) s)) 1) :
    ∃ Θ : QDivisor N,
      (∃ m : ℕ, 0 < m ∧ ∀ x : N, ∃ U : V.Opens, ν.base x ∈ U ∧
        ∃ τ : RationalPluriForms sV 2 m, GeneratesOn B m U τ ∧
          ∃ ρ : RationalPluriForms (ν ≫ sV) 1 m, IsPoincareResidue sV ν 1 m τ ρ ∧
            GeneratesOn Θ m (ν ⁻¹ᵁ U) ρ) ∧
      (∀ Q : Mori.PrimeDivisor N, Θ Q = -((Q.ordForm τN : ℤ) : ℚ) -
        (N.ord (functionFieldMap (ν ≫ g) (ψ ((ν ≫ g) Q.genericPoint))) Q.genericPoint : ℚ) / m₀) ∧
      (∀ (m : ℕ) (a : T.functionField),
        letI := functionFieldAlgebra sV
        letI := functionFieldAlgebra (ν ≫ sV)
        IsPoincareResidue sV ν 1 m (functionFieldMap g a • formPow ω₀ m)
          ((functionFieldMap (ν ≫ g) a * (ε : N.functionField) ^ m) •
            formPow (exteriorPower.ιMulti N.functionField 1 fun _ : Fin 1 =>
              KaehlerDifferential.D k N.functionField (functionFieldMap (ν ≫ g) s)) m)) := by
  classical
  let := functionFieldAlgebra sV
  let := functionFieldAlgebra (ν ≫ sV)
  subst hω₀
  have : QuasiCompact (ν ≫ sV) := inferInstance
  have : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace (ν ≫ sV)
  have hdimN : topologicalKrullDim N = 1 := by
    rw [← hdimT]
    exact (Scheme.homeoOfIso (asIso (ν ≫ g))).isHomeomorph.topologicalKrullDim_eq
  have hgη : g (ν (genericPoint N)) = genericPoint T := by rw [hνη, hPh]
  have hn0 : ((n : ℕ) : N.functionField) ≠ 0 := by
    have : CharZero N.functionField :=
      charZero_of_injective_algebraMap (algebraMap k N.functionField).injective
    exact_mod_cast hn.ne'
  -- residues of pulled-back multiples of powers of `ω₀`
  have hres : ∀ (m : ℕ) (a : T.functionField),
      IsPoincareResidue sV ν 1 m (functionFieldMap g a • formPow ((algebraMap k V.functionField
          (n : k)⁻¹ * f⁻¹) • exteriorPower.ιMulti V.functionField 2
            (Fin.cons (KaehlerDifferential.D k V.functionField f) fun _ : Fin 1 =>
              KaehlerDifferential.D k V.functionField (functionFieldMap g s))) m)
        ((functionFieldMap (ν ≫ g) a * (ε : N.functionField) ^ m) •
          formPow (exteriorPower.ιMulti N.functionField 1 fun _ : Fin 1 =>
            KaehlerDifferential.D k N.functionField (functionFieldMap (ν ≫ g) s)) m) := by
    intro m a
    obtain ⟨c, hc1, hc2⟩ := exists_stalk_eq_functionFieldMap g ν hgη a
    obtain ⟨xs, hx1, hx2⟩ := exists_stalk_eq_functionFieldMap g ν hgη s
    have h := isPoincareResidue_smul_formPow_dlog_of_surjective (sY := sV) (j := ν) P hνη
      (ν.stalkMap_surjective _) hdimV ((n : k)⁻¹)
      hf xs c (by rw [hx2]; exact hs) m
    rw [hc1, hx1, hc2, hx2, hνη, hε] at h
    convert h using 3
    rw [map_inv₀, map_natCast]
    push_cast
    field_simp
  have hιN := ιMulti_fin_one_ne_zero (R := N.functionField) hs
  have hτN0 : τN ≠ 0 := by
    rw [hτN]
    exact formPow_ne_zero_of_ne_zero (sX := ν ≫ sV) hdimN hιN 1
  have hεm : (ε : N.functionField) ^ m₀ = 1 := by
    obtain ⟨j, hj⟩ := hm₀e
    have h2 : (ε : N.functionField) ^ 2 = 1 := by
      have := congrArg (Int.cast : ℤ → N.functionField) hε1
      push_cast at this
      exact this
    rw [hj, ← two_mul, pow_mul, h2, one_pow]
  -- the boundary
  have hφinj : Function.Injective fun Q : Mori.PrimeDivisor N => (ν ≫ g) Q.genericPoint := by
    intro Q Q' h
    have hb : Function.Injective (ν ≫ g).base := (Scheme.homeoOfIso (asIso (ν ≫ g))).injective
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hb h)
  set Θf : Mori.PrimeDivisor N → ℚ := fun Q => -((Q.ordForm τN : ℤ) : ℚ) -
    (N.ord (functionFieldMap (ν ≫ g) (ψ ((ν ≫ g) Q.genericPoint))) Q.genericPoint : ℚ) / m₀
  have hΘfin : (Function.support Θf).Finite := by
    refine ((finite_ordForm_ne_zero τN).union
      (hψfin.preimage hφinj.injOn)).subset fun Q hQ => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_preimage, not_or, not_not] at h
    apply hQ
    simp only [Θf, h.1, h.2, map_one, Scheme.ord_one]
    simp
  set Θ : QDivisor N := Finsupp.ofSupportFinite Θf hΘfin
  have hΘ : ∀ Q, Θ Q = Θf Q := fun Q => rfl
  refine ⟨Θ, ⟨m₀, hm₀, fun x => ?_⟩, hΘ, fun m a => hres m a⟩
  set t := (ν ≫ g) x
  have hxU : ν.base x ∈ g ⁻¹ᵁ W t := hW t
  refine ⟨g ⁻¹ᵁ W t, hxU, functionFieldMap g (ψ t) • formPow ((algebraMap k V.functionField
    (n : k)⁻¹ * f⁻¹) • exteriorPower.ιMulti V.functionField 2
      (Fin.cons (KaehlerDifferential.D k V.functionField f) fun _ : Fin 1 =>
        KaehlerDifferential.D k V.functionField (functionFieldMap g s))) m₀, ⟨?_, ?_⟩, _,
    hres m₀ (ψ t), ⟨?_, ?_⟩⟩
  · exact smul_ne_zero ((map_ne_zero _).mpr (hψ0 t)) (formPow_ne_zero_of_ne_zero hdimV hω0 m₀)
  · intro Γ hΓ
    have e1 := ordForm_smul_formPow hdimV Γ hω0 ((map_ne_zero (functionFieldMap g)).mpr (hψ0 t))
      m₀ _ rfl τ₁ hτ₁
    rw [e1]
    have := hgen t Γ hΓ
    rw [show B.coeff Γ = B Γ from rfl]
    push_cast at this ⊢
    linear_combination this
  · rw [hεm, mul_one]
    exact smul_ne_zero ((map_ne_zero _).mpr (hψ0 t))
      (formPow_ne_zero_of_ne_zero (sX := ν ≫ sV) hdimN hιN m₀)
  · intro Q hQ
    rw [hεm, mul_one, show Θ.coeff Q = Θf Q from rfl]
    have e1 := ordForm_smul_formPow (sX := ν ≫ sV) hdimN Q hιN
      ((map_ne_zero (functionFieldMap (ν ≫ g))).mpr (hψ0 t)) m₀ _ rfl τN hτN
    rw [e1]
    simp only [Θf]
    -- `(ν ≫ g)(η_Q)` lies in `W_t`
    obtain ⟨y, hyQ, hyU⟩ := hQ
    have hyW : (ν ≫ g) y ∈ W t := hyU
    have hQW : (ν ≫ g) Q.genericPoint ∈ W t := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyQ
      have hsp : (ν ≫ g) Q.genericPoint ⤳ (ν ≫ g) y :=
        (specializes_iff_mem_closure.mpr hyQ).map (ν ≫ g).continuous
      exact hsp.mem_open (W t).isOpen hyW
    have hm₀q : (m₀ : ℚ) ≠ 0 := by exact_mod_cast hm₀.ne'
    by_cases hQt : (ν ≫ g) Q.genericPoint = t
    · rw [hQt]
      push_cast
      field_simp
      ring
    · have hψ1 := hWψ t _ hQW hQt
      have hord0 := hWord t _ hQW hQt
      have hne : (ν ≫ g) Q.genericPoint ≠ genericPoint T := by
        intro h
        have hQη : Q.genericPoint = genericPoint N := by
          apply (Scheme.homeoOfIso (asIso (ν ≫ g))).injective
          change (ν ≫ g) Q.genericPoint = (ν ≫ g) (genericPoint N)
          rw [h, Scheme.Hom.comp_apply, hgη]
        have hc : Order.coheight Q.genericPoint = 1 :=
          AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q
        rw [hQη, Order.coheight_eq_zero.mpr (fun y _ => (genericPoint_spec N).specializes trivial)]
          at hc
        exact absurd hc (by norm_num)
      obtain ⟨u, hu, hue⟩ := exists_isUnit_algebraMap_eq_of_ord_eq_zero
        (MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hdimT hne) (hψ0 t) hord0
      have h0 := ord_functionFieldMap_eq_zero_of_isUnit (ν ≫ g) Q hu
      rw [hue] at h0
      rw [hψ1, map_one, Scheme.ord_one, h0]
      simp

/-- A one-fold tensor of a sum is the sum of the one-fold tensors. -/
private theorem formPow_one_add {k K : Type*} [CommRing k] [Field K] [Algebra k K] {d : ℕ}
    (v w : ⋀[K]^d Ω[K⁄k]) : formPow (v + w) 1 = formPow v 1 + formPow w 1 := by
  have h := (PiTensorProduct.tprod K).map_update_add (fun _ : Fin 1 => v) 0 v w
  have e : ∀ z, Function.update (fun _ : Fin 1 => v) 0 z = fun _ => z := fun z => by
    funext i; fin_cases i; simp
  simp only [e] at h
  exact h

/-- Nonzero constants have order zero along a prime divisor. -/
private theorem ord_algebraMap_const_eq_zero {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] (Γ : Mori.PrimeDivisor X)
    {q : k} (hq : q ≠ 0) :
    letI := functionFieldAlgebra sX
    X.ord (algebraMap k X.functionField q) Γ.genericPoint = 0 := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  rw [IsScalarTower.algebraMap_apply k Γ.localRing X.functionField]
  exact Γ.ord_algebraMap_of_isUnit ((IsUnit.mk0 q hq).map _)

/-- **Orders of logarithmic 2-forms.** Along a prime divisor `Γ` of a normal surface, the form
`q f⁻¹ df ∧ dx`, for `x` regular along `Γ`, has order at least `-1`, and at least `0` when `f` has
order zero along `Γ`. -/
private theorem ordForm_dlog_ge {k : Type} [Field k] [PerfectField k] [CharZero k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] (hdim : topologicalKrullDim X = 2) (Γ : Mori.PrimeDivisor X)
    {f : X.functionField} (hf : f ≠ 0) (xO : Γ.localRing) (q : k)
    (τ : RationalPluriForms sX 2 ((1 : ℕ) : ℤ))
    (hτ : letI := functionFieldAlgebra sX
      τ = formPow ((algebraMap k X.functionField q * f⁻¹) • exteriorPower.ιMulti X.functionField 2
        (Fin.cons (KaehlerDifferential.D k X.functionField f) fun _ : Fin 1 =>
          KaehlerDifferential.D k X.functionField (algebraMap Γ.localRing X.functionField xO))) 1)
    (hτ0 : τ ≠ 0) :
    (if X.ord f Γ.genericPoint = 0 then (0 : ℤ) else -1) ≤ Γ.ordForm τ := by
  classical
  let := functionFieldAlgebra sX
  have := Γ.isDiscreteValuationRing_localRing
  obtain ⟨p, hp, hp1⟩ := exists_ord_eq_one Γ.coheight_genericPoint
  obtain ⟨u, hu, hfu⟩ := exists_isUnit_eq_mul_zpow Γ.coheight_genericPoint hp1 hf
  set a := X.ord f Γ.genericPoint
  set pH := algebraMap (X.presheaf.stalk Γ.genericPoint) X.functionField p
  set uH := algebraMap (X.presheaf.stalk Γ.genericPoint) X.functionField u
  set xH := KaehlerDifferential.D k X.functionField (algebraMap Γ.localRing X.functionField xO)
  have hpH0 : pH ≠ 0 := by
    intro h0; rw [h0] at hp1; simp at hp1
  have huH0 : uH ≠ 0 := (hu.map _).ne_zero
  have hq : q ≠ 0 := by
    rintro rfl
    apply hτ0
    rw [hτ, map_zero, zero_mul, zero_smul]
    exact (PiTensorProduct.tprod X.functionField).map_coord_zero (0 : Fin 1) rfl
  set A := exteriorPower.ιMulti X.functionField 2
    (Fin.cons (KaehlerDifferential.D k X.functionField pH) fun _ : Fin 1 => xH)
  set Bf := exteriorPower.ιMulti X.functionField 2
    (Fin.cons (KaehlerDifferential.D k X.functionField uH) fun _ : Fin 1 => xH)
  have hsplit : (algebraMap k X.functionField q * f⁻¹) • exteriorPower.ιMulti X.functionField 2
      (Fin.cons (KaehlerDifferential.D k X.functionField f) fun _ : Fin 1 => xH) =
      (algebraMap k X.functionField q * a * pH⁻¹) • A +
        (algebraMap k X.functionField q * uH⁻¹) • Bf := by
    rw [hfu, ← smul_smul, ← ιMulti_cons_smul, inv_smul_D_mul_zpow (k := k) huH0 hpH0 a,
      ιMulti_cons_add, ιMulti_cons_smul, ιMulti_cons_smul, ιMulti_cons_smul]
    module
  have hτsplit : τ = (formPow ((algebraMap k X.functionField q * a * pH⁻¹) • A) 1 +
      formPow ((algebraMap k X.functionField q * uH⁻¹) • Bf) 1 : RationalPluriForms sX 2 ((1 : ℕ) : ℤ)) := by
    rw [hτ, hsplit, formPow_one_add]
  -- bounds for the two summands
  have hA : ∀ (c : X.functionField) (τ' : RationalPluriForms sX 2 ((1 : ℕ) : ℤ)),
      τ' = formPow (c • A) 1 → τ' ≠ 0 → X.ord c Γ.genericPoint ≤ Γ.ordForm τ' := by
    intro c τ' hτ' h0
    have hc : c ≠ 0 := by
      rintro rfl; apply h0; rw [hτ', zero_smul]
      exact (PiTensorProduct.tprod X.functionField).map_coord_zero (0 : Fin 1) rfl
    have hA0 : A ≠ 0 := by
      rintro h; apply h0; rw [hτ', h, smul_zero]
      exact (PiTensorProduct.tprod X.functionField).map_coord_zero (0 : Fin 1) rfl
    have e1 := ordForm_smul_formPow hdim Γ hA0 hc 1 τ' (by rw [hτ', formPow_smul, pow_one])
      (formPow A 1) rfl
    have e2 := zero_le_ordForm_formPow_ιMulti hdim Γ p xO (formPow A 1) rfl
      (formPow_ne_zero_of_ne_zero hdim hA0 1)
    rw [e1]; push_cast; linarith
  have hB : ∀ (c : X.functionField) (τ' : RationalPluriForms sX 2 ((1 : ℕ) : ℤ)),
      τ' = formPow (c • Bf) 1 → τ' ≠ 0 → X.ord c Γ.genericPoint ≤ Γ.ordForm τ' := by
    intro c τ' hτ' h0
    have hc : c ≠ 0 := by
      rintro rfl; apply h0; rw [hτ', zero_smul]
      exact (PiTensorProduct.tprod X.functionField).map_coord_zero (0 : Fin 1) rfl
    have hB0 : Bf ≠ 0 := by
      rintro h; apply h0; rw [hτ', h, smul_zero]
      exact (PiTensorProduct.tprod X.functionField).map_coord_zero (0 : Fin 1) rfl
    have e1 := ordForm_smul_formPow hdim Γ hB0 hc 1 τ' (by rw [hτ', formPow_smul, pow_one])
      (formPow Bf 1) rfl
    have e2 := zero_le_ordForm_formPow_ιMulti hdim Γ u xO (formPow Bf 1) rfl
      (formPow_ne_zero_of_ne_zero hdim hB0 1)
    rw [e1]; push_cast; linarith
  have hqH := ord_algebraMap_const_eq_zero (sX := sX) Γ hq
  have hqH0 : algebraMap k X.functionField q ≠ 0 := (map_ne_zero _).mpr hq
  have hordu : X.ord uH⁻¹ Γ.genericPoint = 0 := by
    have : X.ord uH Γ.genericPoint = 0 := Γ.ord_algebraMap_of_isUnit hu
    rw [show uH⁻¹ = uH ^ (-1 : ℤ) from (zpow_neg_one uH).symm, MMP.Mori.ord_zpow _ huH0, this,
      mul_zero]
  have hBord : X.ord (algebraMap k X.functionField q * uH⁻¹) Γ.genericPoint = 0 := by
    rw [Scheme.ord_mul hqH0 (inv_ne_zero huH0), hqH, hordu, add_zero]
  by_cases ha : a = 0
  · rw [if_pos ha]
    have hτB : τ = formPow ((algebraMap k X.functionField q * uH⁻¹) • Bf) 1 := by
      rw [hτsplit, ha, Int.cast_zero, mul_zero, zero_mul, zero_smul,
        show (formPow (0 : ⋀[X.functionField]^2 Ω[X.functionField⁄k]) 1 :
          RationalPluriForms sX 2 ((1 : ℕ) : ℤ)) = 0 from
          (PiTensorProduct.tprod X.functionField).map_coord_zero (0 : Fin 1) rfl, zero_add]
    have := hB _ τ hτB hτ0
    rwa [hBord] at this
  · rw [if_neg ha]
    obtain ⟨τA, hτA⟩ : ∃ τA : RationalPluriForms sX 2 ((1 : ℕ) : ℤ),
        τA = formPow ((algebraMap k X.functionField q * a * pH⁻¹) • A) 1 := ⟨_, rfl⟩
    obtain ⟨τB, hτB⟩ : ∃ τB : RationalPluriForms sX 2 ((1 : ℕ) : ℤ),
        τB = formPow ((algebraMap k X.functionField q * uH⁻¹) • Bf) 1 := ⟨_, rfl⟩
    have hτAB : τ = τA + τB := by rw [hτA, hτB]; exact hτsplit
    have hAord : X.ord (algebraMap k X.functionField q * a * pH⁻¹) Γ.genericPoint = -1 := by
      have : CharZero X.functionField :=
        charZero_of_injective_algebraMap (algebraMap k X.functionField).injective
      have ha0 : (a : X.functionField) ≠ 0 := by exact_mod_cast ha
      have hak : (a : k) ≠ 0 := by exact_mod_cast ha
      have haK : (a : X.functionField) = algebraMap k X.functionField (a : k) := by simp
      rw [Scheme.ord_mul (mul_ne_zero hqH0 ha0) (inv_ne_zero hpH0), Scheme.ord_mul hqH0 ha0,
        hqH, haK, ord_algebraMap_const_eq_zero (sX := sX) Γ hak,
        show pH⁻¹ = pH ^ (-1 : ℤ) from (zpow_neg_one pH).symm, MMP.Mori.ord_zpow _ hpH0, hp1]
      norm_num
    by_cases hA0 : τA = 0
    · have := hB _ τ (by rw [hτAB, hA0, zero_add, hτB]) hτ0
      rw [hBord] at this
      linarith
    · have h1 := hA _ τA hτA hA0
      rw [hAord] at h1
      by_cases hB0 : τB = 0
      · rw [hτAB, hB0, add_zero]; exact h1
      · have h2 := hB _ τB hτB hB0
        rw [hBord] at h2
        have hsum : τA + τB ≠ 0 := fun h => hτ0 (hτAB.trans h)
        have h3 := Γ.min_ordForm_le_ordForm_add hsum
        rw [hτAB]
        omega

/-- The extension of function fields of a dominant morphism `f` with `f ≫ s_Y = s_X`, as a
`k`-homomorphism. -/
private noncomputable def functionFieldHomOfEq {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] (h : f ≫ sY = sX) : FunctionFieldHom sX sY := by
  subst h; exact functionFieldHomOf sY f

private theorem functionFieldHomOfEq_apply {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] (h : f ≫ sY = sX) (a : Y.functionField) :
    functionFieldHomOfEq sX sY f h a = functionFieldMap f a := by
  subst h; rfl

/-- A rational function on the base, pulled back, is regular along a horizontal prime divisor. -/
private theorem functionFieldMap_mem_range_of_horizontal {V T : Scheme.{0}} [IsIntegral V]
    [IsIntegral T] (g : V ⟶ T) [IsDominant g] (Γ : Mori.PrimeDivisor V)
    (hΓ : g Γ.genericPoint = genericPoint T) (s : T.functionField) :
    ∃ xO : Γ.localRing, algebraMap Γ.localRing V.functionField xO = functionFieldMap g s := by
  set a' : T.presheaf.stalk (g Γ.genericPoint) :=
    (T.presheaf.stalkSpecializes (show g Γ.genericPoint ⤳ genericPoint T by rw [hΓ])).hom s
  have ha' : algebraMap (T.presheaf.stalk (g Γ.genericPoint)) T.functionField a' = s := by
    change (T.presheaf.stalkSpecializes _ ≫ T.presheaf.stalkSpecializes _).hom s = s
    rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  exact ⟨(g.stalkMap Γ.genericPoint).hom a', by
    rw [← MMP.Mori.functionFieldMap_algebraMap_stalk g Γ.genericPoint a', ha']⟩

/-- The generic point of a prime divisor is not the generic point of the scheme. -/
private theorem PrimeDivisor.genericPoint_ne_genericPoint {N : Scheme.{0}} [IsIntegral N]
    (Q : Mori.PrimeDivisor N) : Q.genericPoint ≠ genericPoint N := by
  intro h
  have hc : Order.coheight Q.genericPoint = 1 :=
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q
  rw [h, Order.coheight_eq_zero.mpr (fun y _ => (genericPoint_spec N).specializes trivial)] at hc
  exact absurd hc (by norm_num)

section BisectionB1

section LocalAlgebra

variable (k : Type*) [Field k] {R : Type*} [CommRing R] [IsLocalRing R] [Algebra k R]

/-- If `a, b` generate the maximal ideal of a local `k`-algebra `R` with `Ω_{κ/k} = 0` and
`Ω_{R/k}` finite, then `da, db` generate `Ω_{R/k}`. -/
private theorem span_D_pair_eq_top [Module.Finite R Ω[R⁄k]]
    [Subsingleton Ω[IsLocalRing.ResidueField R⁄k]] {a b : R}
    (hspan : Ideal.span {a, b} = IsLocalRing.maximalIdeal R) :
    Submodule.span R {KaehlerDifferential.D k R a, KaehlerDifferential.D k R b} = ⊤ := by
  have hr : Set.range ![a, b] = {a, b} := by
    ext z; simp [eq_comm, or_comm]
  have h1 := MMP.Flips.ResolutionInputs.span_tmul_D k (R := R) ![a, b] (by rw [hr]; exact hspan)
  rw [← IsLocalRing.map_tensorProduct_mk_eq_top, Submodule.map_span, eq_top_iff]
  intro v _
  have hv := h1 (Submodule.mem_top (x := v))
  have hsub : Set.range (fun i => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R]
      KaehlerDifferential.D k R (![a, b] i)) ⊆
      ⇑(TensorProduct.mk R (IsLocalRing.ResidueField R) Ω[R⁄k] 1) ''
        {KaehlerDifferential.D k R a, KaehlerDifferential.D k R b} := by
    rintro - ⟨i, rfl⟩
    fin_cases i
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr rfl, rfl⟩
  have hv' := Submodule.span_mono hsub hv
  rw [← Submodule.restrictScalars_mem R,
    Submodule.restrictScalars_span R _ IsLocalRing.residue_surjective] at hv'
  exact hv'

/-- Under the hypotheses of `span_D_pair_eq_top`, `da ∧ db` generates `Ω²_{R/k}`. -/
private theorem span_ιMulti_D_pair_eq_top [Module.Finite R Ω[R⁄k]]
    [Subsingleton Ω[IsLocalRing.ResidueField R⁄k]] {a b : R}
    (hspan : Ideal.span {a, b} = IsLocalRing.maximalIdeal R) :
    Submodule.span R {(exteriorPower.ιMulti R 2
      ![KaehlerDifferential.D k R a, KaehlerDifferential.D k R b])} = ⊤ := by
  have h := exteriorPower.ιMulti_span_of_span (R := R) (n := 2) (M := Ω[R⁄k]) (span_D_pair_eq_top k hspan)
  rw [eq_top_iff, ← h, Submodule.span_le]
  rintro - ⟨v, hv, rfl⟩
  have h0 : v 0 = KaehlerDifferential.D k R a ∨ v 0 = KaehlerDifferential.D k R b :=
    hv ⟨0, rfl⟩
  have h1 : v 1 = KaehlerDifferential.D k R a ∨ v 1 = KaehlerDifferential.D k R b :=
    hv ⟨1, rfl⟩
  have hvv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  set ω := exteriorPower.ιMulti R 2 ![KaehlerDifferential.D k R a, KaehlerDifferential.D k R b]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rw [hvv, h0, h1]
  · rw [(exteriorPower.ιMulti R 2).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)]
    exact zero_mem _
  · exact Submodule.mem_span_singleton_self _
  · have : exteriorPower.ιMulti R 2 ![KaehlerDifferential.D k R b, KaehlerDifferential.D k R a] =
        -ω := by
      have hsw : ![KaehlerDifferential.D k R b, KaehlerDifferential.D k R a] =
          ![KaehlerDifferential.D k R a, KaehlerDifferential.D k R b] ∘
            Equiv.swap (0 : Fin 2) 1 := by
        ext i; fin_cases i <;> rfl
      rw [hsw]
      exact eq_neg_of_add_eq_zero_left
        ((exteriorPower.ιMulti R 2).map_swap_add _ (by decide : (0 : Fin 2) ≠ 1))
    rw [this]
    exact neg_mem (Submodule.mem_span_singleton_self _)
  · rw [(exteriorPower.ιMulti R 2).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)]
    exact zero_mem _

end LocalAlgebra

section Generator

variable {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX]

/-- **A generator at a point has order zero along the prime divisors through it.** If `σ`
generates `Ω^d_{𝒪_{X,x}/k}`, every tensor power of its image in `Ω^d_{k(X)/k}` has order `0`
along every prime divisor through `x`. -/
private theorem ordForm_formPow_topFormsMap_eq_zero {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {x : X}
    {σ : letI := stalkAlgebra sX x; ⋀[X.presheaf.stalk x]^d Ω[X.presheaf.stalk x⁄k]}
    (hσ : letI := stalkAlgebra sX x; Submodule.span (X.presheaf.stalk x) {σ} = ⊤)
    (E : Mori.PrimeDivisor X) (hxE : x ∈ E.support) (a : ℕ) :
    letI := stalkAlgebra sX x
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX x
    E.ordForm (show RationalPluriForms sX d (a : ℕ) from
      formPow (topFormsMap k (X.presheaf.stalk x) X.functionField d σ) a) = 0 := by
  let := stalkAlgebra sX x
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX x
  have hsp : E.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hxE
  let := stalkAlgebra sX E.genericPoint
  have := isScalarTower_stalk_functionField sX E.genericPoint
  let : Algebra (X.presheaf.stalk x) E.localRing := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have : IsScalarTower k (X.presheaf.stalk x) E.localRing :=
    MMP.Threefold.Resolution.isScalarTower_stalkSpecializes sX hsp
  have : IsScalarTower (X.presheaf.stalk x) E.localRing X.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => (MMP.Mori.algebraMap_stalkSpecializes hsp r).symm
  have := MMP.Intersection.isLocalization_stalkSpecializes hsp
  set σ' := topFormsMap k (X.presheaf.stalk x) E.localRing d σ with hσ'def
  have hσ' : Submodule.span E.localRing {σ'} = ⊤ :=
    span_singleton_topFormsMap ((IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint)).comap
      (X.presheaf.stalkSpecializes hsp).hom).primeCompl hσ
  have hcomp : topFormsMap k E.localRing X.functionField d σ' =
      topFormsMap k (X.presheaf.stalk x) X.functionField d σ :=
    MMP.Threefold.Mori.Helpers.topFormsMap_comp σ
  have h0 : topFormsMap k E.localRing X.functionField d σ' ≠ 0 := E.topFormsMap_ne_zero hd hσ'
  rw [MMP.Mori.PrimeDivisor.ordForm_eq E _ hσ' h0]
  have h1 : formCoeff E.localRing hσ' h0 (formPow (topFormsMap k (X.presheaf.stalk x)
      X.functionField d σ) a : PluriForms k X.functionField d ((a : ℕ) : ℤ)) = 1 := by
    rw [formCoeff, ← hcomp, ← topFormsBasis_apply hσ' h0 (),
      ← ZTensorPower.basis_natCast]
    simp
  erw [h1]
  exact (Scheme.ord_eq_iff (n := 0) E.coheight_genericPoint one_ne_zero).2 (by simp)

omit [PerfectField k] [LocallyOfFiniteType sX] in
/-- On a normal scheme, a rational function of order zero along every prime divisor through `x`
is a unit of `𝒪_{X,x}`. -/
private theorem exists_isUnit_algebraMap_eq_of_forall_ord_eq_zero (x : X) {f : X.functionField}
    (hf : f ≠ 0) (h : ∀ E : Mori.PrimeDivisor X, x ∈ E.support → X.ord f E.genericPoint = 0) :
    ∃ u : X.presheaf.stalk x, IsUnit u ∧ algebraMap _ X.functionField u = f := by
  obtain ⟨r, hr⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
    x hf fun E hE => (h E hE).ge
  obtain ⟨r', hr'⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
    x (inv_ne_zero hf) fun E hE => by
      rw [show f⁻¹ = f ^ (-1 : ℤ) from (zpow_neg_one f).symm, MMP.Mori.ord_zpow _ hf, h E hE,
        mul_zero]
  refine ⟨r, IsUnit.of_mul_eq_one r' ?_, hr⟩
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [map_mul, hr, hr', mul_inv_cancel₀ hf, map_one]

end Generator

section LocalEquation

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The ideal of a prime divisor `E` in `𝒪_{X,x}` is the prime of the generic point of `E`: the
elements whose generization to `𝒪_{X,E}` lies in the maximal ideal. -/
private theorem stalk_idealSheaf_eq_comap (E : Mori.PrimeDivisor X) {x : X} (hx : x ∈ E.support)
    (hsp : E.genericPoint ⤳ x) :
    IdealSheafData.stalk E.idealSheaf x = (IsLocalRing.maximalIdeal
      (X.presheaf.stalk E.genericPoint)).comap (X.presheaf.stalkSpecializes hsp).hom := by
  obtain ⟨q, hq, hI, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E hx
  rw [hI, ← MMP.Intersection.comap_maximalIdeal_stalkSpecializes_fromSpecStalk x q]
  have key : ∀ (z : X) (h : z ⤳ x), z = E.genericPoint →
      (IsLocalRing.maximalIdeal (X.presheaf.stalk z)).comap (X.presheaf.stalkSpecializes h).hom =
        (IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint)).comap
          (X.presheaf.stalkSpecializes hsp).hom := by
    rintro z h rfl; rfl
  exact key _ _ hq

private theorem genericPoint_specializes_of_mem_support' (E : Mori.PrimeDivisor X) {x : X}
    (hx : x ∈ E.support) : E.genericPoint ⤳ x := by
  rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact hx

variable [IsNormal X]

/-- An element of `𝒪_{X,x}` has order `0` along a prime divisor `E ∋ x` exactly when it is
outside the ideal of `E`. -/
private theorem ord_eq_zero_of_notMem_stalk_idealSheaf (E : Mori.PrimeDivisor X) {x : X}
    (hx : x ∈ E.support) {a : X.presheaf.stalk x}
    (ha : a ∉ IdealSheafData.stalk E.idealSheaf x) :
    X.ord (algebraMap _ X.functionField a) E.genericPoint = 0 := by
  have hsp := genericPoint_specializes_of_mem_support' E hx
  rw [stalk_idealSheaf_eq_comap E hx hsp, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, not_not] at ha
  rw [← MMP.Mori.algebraMap_stalkSpecializes hsp]
  exact E.ord_algebraMap_of_isUnit ha

/-- **Prime local equations at a factorial point.** If `𝒪_{X,x}` is factorial, a prime divisor
`E ∋ x` has a local equation `p` at `x`: `p` generates the ideal of `E` in `𝒪_{X,x}`, has order one
along `E` and order zero along every other prime divisor through `x`. -/
private theorem exists_localEquation_of_uniqueFactorizationMonoid {x : X}
    [UniqueFactorizationMonoid (X.presheaf.stalk x)] (E : Mori.PrimeDivisor X)
    (hx : x ∈ E.support) :
    ∃ p : X.presheaf.stalk x, IdealSheafData.stalk E.idealSheaf x = Ideal.span {p} ∧
      X.ord (algebraMap _ X.functionField p) E.genericPoint = 1 ∧
      ∀ E' : Mori.PrimeDivisor X, x ∈ E'.support → E' ≠ E →
        X.ord (algebraMap _ X.functionField p) E'.genericPoint = 0 := by
  obtain ⟨q, hq, hI, hht⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E hx
  have hq0 : q.asIdeal ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.height_bot] at hht
    exact zero_ne_one hht
  obtain ⟨p, hpq, hp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot q.isPrime hq0
  have hspan : ∀ I : Ideal (X.presheaf.stalk x), I.IsPrime → I.height = 1 → p ∈ I →
      I = Ideal.span {p} := by
    intro I hI hIh hpI
    have hle : Ideal.span {p} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hpI
    haveI hpr : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    by_contra hne
    have hlt : Ideal.span {p} < I := lt_of_le_of_ne hle (Ne.symm hne)
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have hbot : (⊥ : Ideal (X.presheaf.stalk x)) < Ideal.span {p} := by
      rw [bot_lt_iff_ne_bot]
      intro h
      rw [Ideal.span_singleton_eq_bot] at h
      exact hp.ne_zero h
    haveI : (⊥ : Ideal (X.presheaf.stalk x)).IsPrime := Ideal.isPrime_bot
    have h0 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
    have h2 : (1 : ℕ∞) ≤ (Ideal.span {p}).height := le_trans le_add_self h0
    rw [hIh] at h1
    have : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add h2 le_rfl).trans h1
    norm_num at this
  have hIE : IdealSheafData.stalk E.idealSheaf x = Ideal.span {p} := by
    rw [hI]; exact hspan _ q.isPrime hht hpq
  refine ⟨p, hIE, ?_, ?_⟩
  · -- `p` is a uniformizer of the discrete valuation ring `𝒪_{X,E}`
    have hsp := genericPoint_specializes_of_mem_support' E hx
    have := E.isDiscreteValuationRing_localRing
    letI := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
    have hloc := MMP.Intersection.isLocalization_stalkSpecializes hsp
    have hcomap := stalk_idealSheaf_eq_comap E hx hsp
    set Q := (IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint)).comap
      (X.presheaf.stalkSpecializes hsp).hom
    have hQ : Q = Ideal.span {p} := hcomap.symm.trans hIE
    have hmap : (IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint)) =
        Ideal.span {algebraMap _ (X.presheaf.stalk E.genericPoint) p} := by
      rw [← Set.image_singleton, ← Ideal.map_span, ← hQ]
      exact (IsLocalization.AtPrime.map_eq_maximalIdeal Q _).symm
    have hirr : Irreducible (algebraMap _ (X.presheaf.stalk E.genericPoint) p) :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmap
    have hne : algebraMap (X.presheaf.stalk E.genericPoint) X.functionField
        (algebraMap _ (X.presheaf.stalk E.genericPoint) p) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hirr.ne_zero
    have e := (Scheme.ord_eq_iff E.coheight_genericPoint hne).mpr (Ring.ordFrac_irreducible hirr)
    rwa [show algebraMap (X.presheaf.stalk E.genericPoint) X.functionField
        (algebraMap _ (X.presheaf.stalk E.genericPoint) p) =
        algebraMap (X.presheaf.stalk x) X.functionField p from
      MMP.Mori.algebraMap_stalkSpecializes hsp p] at e
  · intro E' hxE' hne
    apply ord_eq_zero_of_notMem_stalk_idealSheaf E' hxE'
    intro hpE'
    obtain ⟨q', hq', hI', hht'⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E' hxE'
    have h1 : IdealSheafData.stalk E'.idealSheaf x = Ideal.span {p} := by
      rw [hI'] at hpE' ⊢; exact hspan _ q'.isPrime hht' hpE'
    exact hne (MMP.Intersection.eq_of_stalk_idealSheaf_eq hxE' hx (h1.trans hIE.symm))

end LocalEquation

section Smooth

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- The local ring at a point of the smooth locus is regular. -/
private theorem isRegularLocalRing_stalk_of_mem_smoothLocus {x : X} (hx : x ∈ Mori.smoothLocus sX) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hxU, hU⟩ := MMP.Mori.mem_smoothLocus_iff.1 hx
  have : Smooth (U.ι ≫ sX) := hU
  have := isRegularLocalRing_stalk_of_smooth_over_field (U.ι ≫ sX) ⟨x, hxU⟩
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨x, hxU⟩).commRingCatIsoToRingEquiv

end Smooth

end BisectionB1

section BisectionB2

section Valuation

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- `ord_E f ≥ 0` is `v_E(f) ≤ 1`. -/
private theorem zero_le_ord_iff (E : Mori.PrimeDivisor X) {f : X.functionField} (hf : f ≠ 0) :
    0 ≤ X.ord f E.genericPoint ↔ E.divisorialValuation f ≤ 1 := by
  rw [E.divisorialValuation_eq_exp_neg_ord hf, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

/-- `ord_E f ≥ 1` is `v_E(f) < 1`. -/
private theorem one_le_ord_iff (E : Mori.PrimeDivisor X) {f : X.functionField} (hf : f ≠ 0) :
    1 ≤ X.ord f E.genericPoint ↔ E.divisorialValuation f < 1 := by
  rw [E.divisorialValuation_eq_exp_neg_ord hf, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

/-- If `f` and `g` have nonnegative order along `E`, so does `f - g` (when nonzero). -/
private theorem zero_le_ord_sub (E : Mori.PrimeDivisor X) {f g : X.functionField} (hfg : f - g ≠ 0)
    (hf : f = 0 ∨ 0 ≤ X.ord f E.genericPoint) (hg : g = 0 ∨ 0 ≤ X.ord g E.genericPoint) :
    0 ≤ X.ord (f - g) E.genericPoint := by
  have hf' : E.divisorialValuation f ≤ 1 := by
    rcases hf with rfl | hf
    · simp
    · by_cases h0 : f = 0
      · simp [h0]
      · exact (zero_le_ord_iff E h0).mp hf
  have hg' : E.divisorialValuation g ≤ 1 := by
    rcases hg with rfl | hg
    · simp
    · by_cases h0 : g = 0
      · simp [h0]
      · exact (zero_le_ord_iff E h0).mp hg
  rw [zero_le_ord_iff E hfg]
  exact (Valuation.map_sub _ _ _).trans (max_le hf' hg')

/-- The image of an element of the maximal ideal of `𝒪_{X,E}` has positive order along `E`. -/
private theorem one_le_ord_algebraMap_of_mem (E : Mori.PrimeDivisor X) {a : E.localRing}
    (ha : a ∈ IsLocalRing.maximalIdeal E.localRing)
    (ha0 : algebraMap E.localRing X.functionField a ≠ 0) :
    1 ≤ X.ord (algebraMap E.localRing X.functionField a) E.genericPoint :=
  (one_le_ord_iff E ha0).mpr ((E.divisorialValuation_algebraMap_lt_one_iff a).mpr ha)

/-- An element of `𝒪_{X,E}` has nonnegative order along `E`. -/
private theorem zero_le_ord_algebraMap_localRing (E : Mori.PrimeDivisor X) {a : E.localRing}
    (ha : algebraMap E.localRing X.functionField a ≠ 0) :
    0 ≤ X.ord (algebraMap E.localRing X.functionField a) E.genericPoint :=
  (zero_le_ord_iff E ha).mpr ((E.divisorialValuation_le_one_iff _).mpr ⟨a, rfl⟩)

/-- If `h ≡ 1` at `E`, then `h^m ≡ 1` at `E`. -/
private theorem one_le_ord_pow_sub_one (E : Mori.PrimeDivisor X) {h : X.functionField}
    (hh : h - 1 = 0 ∨ 1 ≤ X.ord (h - 1) E.genericPoint) (m : ℕ) :
    h ^ m - 1 = 0 ∨ 1 ≤ X.ord (h ^ m - 1) E.genericPoint := by
  by_cases h0 : h ^ m - 1 = 0
  · exact Or.inl h0
  right
  rw [one_le_ord_iff E h0]
  have hv : E.divisorialValuation (h - 1) < 1 := by
    rcases hh with hh | hh
    · rw [hh, map_zero]; exact zero_lt_one
    · by_cases hz : h - 1 = 0
      · rw [hz, map_zero]; exact zero_lt_one
      · exact (one_le_ord_iff E hz).mp hh
  have hvh : E.divisorialValuation h ≤ 1 := by
    have : h = (h - 1) + 1 := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le hv.le (by rw [map_one]))
  have hsum : E.divisorialValuation (∑ i ∈ Finset.range m, h ^ i) ≤ 1 := by
    refine (Valuation.map_sum_le _ fun i _ => ?_)
    rw [map_pow]; exact pow_le_one₀ zero_le' hvh
  rw [← geom_sum_mul, map_mul]
  calc E.divisorialValuation (∑ i ∈ Finset.range m, h ^ i) * E.divisorialValuation (h - 1)
      ≤ 1 * E.divisorialValuation (h - 1) := by gcongr
    _ < 1 := by rw [one_mul]; exact hv

/-- A nonzero constant multiple of a function with positive order has positive order. -/
private theorem one_le_ord_mul_of_ord_eq_zero (E : Mori.PrimeDivisor X) {a f : X.functionField}
    (ha : a = 0 ∨ X.ord a E.genericPoint = 0) (hf : f = 0 ∨ 1 ≤ X.ord f E.genericPoint) :
    a * f = 0 ∨ 1 ≤ X.ord (a * f) E.genericPoint := by
  by_cases ha0 : a = 0
  · left; rw [ha0, zero_mul]
  by_cases hf0 : f = 0
  · left; rw [hf0, mul_zero]
  right
  rw [Scheme.ord_mul ha0 hf0, ha.resolve_left ha0, zero_add]
  exact hf.resolve_left hf0

end Valuation

section ClosedPoint

variable {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
  [LocallyOfFiniteType sX]

/-- At a closed point of a scheme locally of finite type over an algebraically closed field `k`,
every element of the local ring is congruent to a constant modulo the maximal ideal. -/
private theorem exists_sub_algebraMap_mem_maximalIdeal {x : X} (hx : IsClosed ({x} : Set X))
    (b : X.presheaf.stalk x) :
    letI := stalkAlgebra sX x
    ∃ c : k, b - algebraMap k _ c ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  letI := stalkAlgebra sX x
  have hfin := MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sX x hx
  obtain ⟨c, hc⟩ := IsSepClosed.algebraMap_surjective k
    (IsLocalRing.ResidueField (X.presheaf.stalk x)) (IsLocalRing.residue _ b)
  refine ⟨c, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hc]
  exact IsScalarTower.algebraMap_apply k (X.presheaf.stalk x)
    (IsLocalRing.ResidueField (X.presheaf.stalk x)) c

end ClosedPoint

section Curve

variable {k : Type} [Field k] [IsAlgClosed k] {C : Scheme.{0}} {sC : C ⟶ Spec (.of k)}
  [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]

/-- **Two logarithmic differentials at a point.** If `w` and `p` are both local parameters at
`R`, then `(dw/w)^{⊗m} = h^m (dp/p)^{⊗m}` with `h ≡ 1` at `R`. -/
private theorem exists_dlogPow_eq_pow_smul (hC : IsNormalVariety k sC)
    (hdim : topologicalKrullDim C = 1) (R : Mori.PrimeDivisor C) {w p : C.functionField}
    (hw : C.ord w R.genericPoint = 1) (hp : C.ord p R.genericPoint = 1) (m : ℕ) :
    ∃ h : C.functionField, (h - 1 = 0 ∨ 1 ≤ C.ord (h - 1) R.genericPoint) ∧
      MMP.Flips.dlogPow sC w m = h ^ m • MMP.Flips.dlogPow sC p m := by
  letI := functionFieldAlgebra sC
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  have hd1 : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdim
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  set e := w * p⁻¹ with hedef
  have he0 : e ≠ 0 := mul_ne_zero hw0 (inv_ne_zero hp0)
  have hwe : w = p * e := by rw [hedef]; field_simp
  have heord : C.ord e R.genericPoint = 0 := by
    rw [hedef, Scheme.ord_mul hw0 (inv_ne_zero hp0),
      show p⁻¹ = p ^ (-1 : ℤ) from (zpow_neg_one p).symm, MMP.Mori.ord_zpow _ hp0, hw, hp]
    norm_num
  -- `de = r dp` with `r` regular at `R`
  obtain ⟨ωp0, ωpR⟩ := MMP.Flips.ordForm_d_eq_zero hC hdim R p hp _ rfl
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hC (n := 1) hd1
  set dp := exteriorPower.ιMulti C.functionField 1 fun _ : Fin 1 =>
    KaehlerDifferential.D k C.functionField p with hdp
  set de := exteriorPower.ιMulti C.functionField 1 fun _ : Fin 1 =>
    KaehlerDifferential.D k C.functionField e with hde
  have hdp0 : dp ≠ 0 := by
    intro h0; apply ωp0
    rw [show (PiTensorProduct.tprod C.functionField fun _ : Fin 1 => dp) =
      PiTensorProduct.tprod C.functionField fun _ : Fin 1 => 0 by rw [h0]]
    exact (PiTensorProduct.tprod C.functionField).map_coord_zero (0 : Fin 1) rfl
  have hcp : b.repr dp () ≠ 0 := by
    intro h0; apply hdp0
    rw [← basis_unit_repr_smul b dp, h0, zero_smul]
  set r := b.repr de () / b.repr dp () with hrdef
  have hr : de = r • dp := by
    conv_lhs => rw [← basis_unit_repr_smul b de]
    conv_rhs => rw [← basis_unit_repr_smul b dp]
    rw [smul_smul, hrdef, div_mul_cancel₀ _ hcp]
  have hrord : r = 0 ∨ 0 ≤ C.ord r R.genericPoint := by
    by_cases hr0 : r = 0
    · exact Or.inl hr0
    right
    obtain ⟨τde, hτde⟩ : ∃ τ : RationalPluriForms sC 1 ((1 : ℕ) : ℤ),
        τ = PiTensorProduct.tprod C.functionField fun _ : Fin 1 => de := ⟨_, rfl⟩
    obtain ⟨τdp, hτdp⟩ : ∃ τ : RationalPluriForms sC 1 ((1 : ℕ) : ℤ),
        τ = PiTensorProduct.tprod C.functionField fun _ : Fin 1 => dp := ⟨_, rfl⟩
    have hτ : τde = r • τdp := by
      rw [hτde, hτdp, hr]
      exact (tprod_const_smul (n := 1) r dp).trans (by rw [pow_one] <;> rfl)
    have hτdp0 : τdp ≠ 0 := hτdp ▸ ωp0
    have hde0 : τde ≠ 0 := by
      rw [hτ]; exact smul_ne_zero hr0 hτdp0
    have h1 := MMP.Flips.zero_le_ordForm_d hC hdim R e heord.ge τde hτde hde0
    have h2 : R.ordForm τde = C.ord r R.genericPoint + R.ordForm τdp := by
      rw [hτ]; exact R.ordForm_smul_of_topologicalKrullDim_eq hd1 hr0 hτdp0
    have hωR' : R.ordForm τdp = 0 := by rw [hτdp]; exact ωpR
    rw [h2, hωR', add_zero] at h1
    exact h1
  -- `w⁻¹ dw = (1 + p e⁻¹ r) p⁻¹ dp`
  set h := 1 + p * e⁻¹ * r with hhdef
  refine ⟨h, ?_, ?_⟩
  · rw [hhdef, add_sub_cancel_left]
    by_cases hr0 : r = 0
    · left; rw [hr0, mul_zero]
    right
    rcases hrord with h0 | h0
    · exact absurd h0 hr0
    rw [Scheme.ord_mul (mul_ne_zero hp0 (inv_ne_zero he0)) hr0,
      Scheme.ord_mul hp0 (inv_ne_zero he0),
      show e⁻¹ = e ^ (-1 : ℤ) from (zpow_neg_one e).symm, MMP.Mori.ord_zpow _ he0, heord, hp]
    omega
  · have key : w⁻¹ • exteriorPower.ιMulti C.functionField 1
        (fun _ : Fin 1 => KaehlerDifferential.D k C.functionField w) =
        h • (p⁻¹ • dp) := by
      apply (exteriorPower.oneEquiv C.functionField Ω[C.functionField⁄k]).injective
      have hre : KaehlerDifferential.D k C.functionField e =
          r • KaehlerDifferential.D k C.functionField p := by
        have := congrArg (exteriorPower.oneEquiv C.functionField Ω[C.functionField⁄k]) hr
        simpa [hde, hdp, exteriorPower.oneEquiv_ιMulti] using this
      simp only [map_smul, hdp, exteriorPower.oneEquiv_ιMulti]
      rw [hwe, Derivation.leibniz, hre, smul_smul, ← add_smul, smul_smul, smul_smul]
      congr 1
      rw [hhdef]
      field_simp
      ring
    unfold MMP.Flips.dlogPow
    simp only
    rw [key, show (fun _ : Fin m => h • (p⁻¹ • dp)) =
      fun i => (fun _ : Fin m => h) i • (fun _ : Fin m => p⁻¹ • dp) i from rfl,
      MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl

/-- **The degree of a pluricanonical form on a curve of genus zero.** On a smooth proper curve of
genus zero, the divisor of a nonzero rational `m`-canonical form has degree `-2m`. -/
private theorem sum_divisorOfForm_eq_of_genus_zero [CompactSpace C] (hC : IsNormalVariety k sC)
    (hsm : IsSmoothScheme sC) (hp : IsProper sC) (hdim : topologicalKrullDim C = 1)
    {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1) (hg : K.h0 k sC = 0) {m : ℕ}
    {ξ : RationalPluriForms sC 1 m} (hξ : ξ ≠ 0) :
    ((divisorOfForm ξ).sum fun _ a => a) = -2 * m := by
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  obtain ⟨φ, hφ⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hC hK hξ
  have h1 := MMP.Flips.sum_principalDivisor_eq_zero hC hsm hp hdim φ
  rw [← hφ] at h1
  have h2 : ∀ D : Divisor C, (D.sum fun _ a => a) =
      Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ) D :=
    fun D => by rw [Finsupp.liftAddHom_apply]; rfl
  have hK2 : (K.sum fun _ a => a) = -2 := by
    have h3 := MMP.Flips.sum_coeff_canonical_eq hC hsm hp hK
    rw [hg] at h3
    have h4 : (K.sum fun _ a => (a : ℚ)) = (((K.sum fun _ a => a : ℤ)) : ℚ) := by
      simp [Finsupp.sum]
    rw [h4] at h3
    exact_mod_cast (by simpa using h3 : ((K.sum fun _ a => a : ℤ) : ℚ) = -2)
  rw [h2, map_sub, map_zsmul, ← h2 K, hK2, ← h2, smul_eq_mul] at h1
  linarith

end Curve

end BisectionB2

section BisectionB3

variable {k : Type} [Field k] {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of k))

/-- An isomorphism over `k` with the glued projective line is an isomorphism over `k` with
`ℙ¹_{Spec k}`. -/
private noncomputable def overIsoOfIsoProjectiveLine (e : projectiveLine k ≅ Z)
    (he : e.hom ≫ sZ = projectiveLine k ↘ Spec (.of k)) :
    Over.mk sZ ≅ Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) :=
  Over.isoMk (e.symm ≪≫ projectiveLineIsoProjectiveSpaceOver k) (by
    simp only [Over.mk_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      projectiveLineIsoProjectiveSpaceOver_hom_fst, ← he, Iso.inv_hom_id_assoc])

/-- A scheme isomorphic over `k` to the projective line is a smooth proper curve, normal as a
scheme. -/
private theorem smooth_isNormal_of_iso_projectiveLine (e : projectiveLine k ≅ Z)
    (he : e.hom ≫ sZ = projectiveLine k ↘ Spec (.of k)) :
    Smooth sZ ∧ IsNormal Z ∧ IsProper sZ ∧ topologicalKrullDim Z = 1 ∧
      AlgebraicGeometry.IsCurve k sZ := by
  set e' := overIsoOfIsoProjectiveLine sZ e he
  have hsm := ProjectiveLineCriterion.smooth_of_iso_projectiveLine e'
  refine ⟨hsm, ?_, ProjectiveLineCriterion.isProper_of_iso_projectiveLine e',
    ProjectiveLineCriterion.topologicalKrullDim_of_iso_projectiveLine e',
    ProjectiveLineCriterion.isCurve_of_iso_projectiveLine e'⟩
  haveI := hsm
  exact isNormal_of_smooth_over_field sZ

/-- **A projective line has genus zero**: on a scheme isomorphic over `k` to `ℙ¹_k`, every
canonical divisor has `h⁰ = 0`. -/
private theorem h0_canonical_eq_zero_of_iso_projectiveLine [IsAlgClosed k] [IsLocallyNoetherian Z]
    [IsNormal Z] (e : projectiveLine k ≅ Z) (he : e.hom ≫ sZ = projectiveLine k ↘ Spec (.of k))
    (hZ : IsNormalVariety k sZ) {K : Divisor Z} (hK : K.IsCanonicalDivisor sZ 1) :
    K.h0 k sZ = 0 := by
  obtain ⟨hsm, -, hp, -, -⟩ := smooth_isNormal_of_iso_projectiveLine sZ e he
  have hsm' : IsSmoothScheme sZ := MMP.Mori.isSmoothScheme_of_smooth hsm
  rw [MMP.Flips.h0_canonical_eq_genus hZ hsm' hp hK]
  have hU : smoothLocus sZ = ⊤ := hsm'
  have key : ∀ U : Z.Opens, U = ⊤ → genus (U.ι ≫ sZ) = 0 := by
    intro U hU'
    subst hU'
    have : IsIso (⊤ : Z.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
    have e'' : Over.mk ((⊤ : Z.Opens).ι ≫ sZ) ≅
        Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) :=
      (Over.isoMk (asIso (⊤ : Z.Opens).ι) rfl : Over.mk ((⊤ : Z.Opens).ι ≫ sZ) ≅ Over.mk sZ) ≪≫
        overIsoOfIsoProjectiveLine sZ e he
    exact ProjectiveLineCriterion.genus_of_iso_projectiveLine e''
  exact key _ hU

end BisectionB3

section BisectionB4

/-- **Generators of the maximal ideal through a quotient.** If `φ : R → S` is a surjective local
homomorphism of local rings with kernel `(t)` and `φ a` generates the maximal ideal of `S`, then
`t, a` generate the maximal ideal of `R`. -/
private theorem span_pair_eq_maximalIdeal_of_surjective {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] (hφ : Function.Surjective φ)
    {t a : R} (hker : RingHom.ker φ = Ideal.span {t})
    (ha : IsLocalRing.maximalIdeal S = Ideal.span {φ a}) :
    Ideal.span {t, a} = IsLocalRing.maximalIdeal R := by
  have hmem : ∀ x : R, φ x ∈ IsLocalRing.maximalIdeal S → x ∈ IsLocalRing.maximalIdeal R :=
    fun x hx => (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp hx (hu.map φ)
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · apply hmem
      have : φ z = 0 := by
        rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _
      rw [this]; exact zero_mem _
    · apply hmem
      rw [ha]; exact Ideal.mem_span_singleton_self _
  · intro z hz
    have hφz : φ z ∈ IsLocalRing.maximalIdeal S :=
      (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
        (IsLocalRing.mem_maximalIdeal _).mp hz ((isUnit_map_iff φ z).mp hu)
    rw [ha, Ideal.mem_span_singleton'] at hφz
    obtain ⟨r, hr⟩ := hφz
    obtain ⟨b, rfl⟩ := hφ r
    have hk : z - b * a ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_sub, map_mul, hr, sub_self]
    rw [hker, Ideal.mem_span_singleton'] at hk
    obtain ⟨c, hc⟩ := hk
    rw [show z = c * t + b * a by linear_combination -hc]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))

/-- The stalks of a scheme locally of finite type over `k` are essentially of finite type. -/
private theorem essFiniteType_stalk {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (x : X) :
    letI := stalkAlgebra sX x
    Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  obtain ⟨W, hW, hpW, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.stalkAlgebra sX x
  let : Algebra Γ(X, W) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hpW⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hW.primeIdealOf ⟨x, hpW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨x, hpW⟩
  have : IsScalarTower k Γ(X, W) (X.presheaf.stalk x) :=
    MMP.Mori.isScalarTower_section_stalk sX W ⟨x, hpW⟩
  have : Algebra.FiniteType k Γ(X, W) := MMP.Mori.finiteType_sectionAlgebra sX hW
  have : Algebra.EssFiniteType Γ(X, W) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization _ (hW.primeIdealOf ⟨x, hpW⟩).asIdeal.primeCompl
  exact Algebra.EssFiniteType.comp k Γ(X, W) _

/-- At a closed point of a scheme locally of finite type over an algebraically closed field, the
residue field has no differentials over `k`. -/
private theorem subsingleton_kaehler_residueField {k : Type} [Field k] [IsAlgClosed k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {x : X}
    (hx : IsClosed ({x} : Set X)) :
    letI := stalkAlgebra sX x
    Subsingleton Ω[IsLocalRing.ResidueField (X.presheaf.stalk x)⁄k] := by
  letI := stalkAlgebra sX x
  have hsurj : Function.Surjective (algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x))) := by
    intro r
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_maximalIdeal sX hx b
    refine ⟨c, ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hc
    rw [IsScalarTower.algebraMap_apply k (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x))]
    exact hc.symm
  have : Algebra.FormallyUnramified k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId k _) hsurj
  infer_instance

/-- **A presentation of a form at a smooth closed point.** Let `y` be a closed point of a normal
surface over an algebraically closed field, `a, b` generators of the maximal ideal of `𝒪_{V,y}`,
and `Ω` a rational `m`-canonical form whose order along every prime divisor `E ∋ y` is `m` times
the order of a rational function `f`. Then `Ω = c (f da ∧ db)^{⊗m}` with `c` a unit of
`𝒪_{V,y}`. -/
private theorem exists_isUnit_smul_formPow_of_span {k : Type} [Field k] [IsAlgClosed k]
    {V : Scheme.{0}} {sV : V ⟶ Spec (.of k)} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [LocallyOfFiniteType sV] (hdimV : topologicalKrullDim V = 2) {y : V}
    (hyc : IsClosed ({y} : Set V)) {a b : V.presheaf.stalk y}
    (hspan : Ideal.span {a, b} = IsLocalRing.maximalIdeal (V.presheaf.stalk y)) {m : ℕ}
    (Ω : RationalPluriForms sV 2 m) (hΩ0 : Ω ≠ 0) {f : V.functionField} (hf : f ≠ 0)
    (hord : ∀ E : Mori.PrimeDivisor V, y ∈ E.support →
      E.ordForm Ω = m * V.ord f E.genericPoint) :
    letI := stalkAlgebra sV y
    letI := functionFieldAlgebra sV
    ∃ c : V.presheaf.stalk y, IsUnit c ∧
      Ω = (algebraMap _ V.functionField c • formPow (f • exteriorPower.ιMulti V.functionField 2
        (Fin.cons (KaehlerDifferential.D k V.functionField (algebraMap _ _ a))
          fun _ : Fin 1 => KaehlerDifferential.D k V.functionField (algebraMap _ _ b))) m :
        RationalPluriForms sV 2 m) := by
  letI := stalkAlgebra sV y
  letI := functionFieldAlgebra sV
  haveI := isScalarTower_stalk_functionField sV y
  have := essFiniteType_stalk sV y
  have := subsingleton_kaehler_residueField sV hyc
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sV) (d := 2)
    (by rw [hdimV]; rfl)
  -- the generator `da ∧ db` of `Ω²_{𝒪_{V,y}}`
  set σ := exteriorPower.ιMulti (V.presheaf.stalk y) 2
    ![KaehlerDifferential.D k (V.presheaf.stalk y) a, KaehlerDifferential.D k _ b] with hσdef
  have hσ : Submodule.span (V.presheaf.stalk y) {σ} = ⊤ := span_ιMulti_D_pair_eq_top k hspan
  set ω : ⋀[V.functionField]^2 Ω[V.functionField⁄k] := exteriorPower.ιMulti V.functionField 2
    (Fin.cons (KaehlerDifferential.D k V.functionField (algebraMap _ _ a))
      fun _ : Fin 1 => KaehlerDifferential.D k V.functionField (algebraMap _ _ b)) with hωdef
  have hσω : topFormsMap k (V.presheaf.stalk y) V.functionField 2 σ = ω := by
    rw [hσdef, topFormsMap_ιMulti, hωdef]
    congr 1
    ext i
    fin_cases i <;> simp [KaehlerDifferential.map_D]
  obtain ⟨bF⟩ := exists_basis_topForms (sX := sV) (d := 2) (by rw [hdimV]; norm_cast)
  have : Nontrivial (⋀[V.functionField]^2 Ω[V.functionField⁄k]) := ⟨⟨bF (), 0, bF.ne_zero ()⟩⟩
  have hω0 : ω ≠ 0 := hσω ▸ topFormsMap_ne_zero_of_span_eq_top hσ
  have hfω0 : f • ω ≠ 0 := smul_ne_zero hf hω0
  -- the coordinate of `Ω` along `(f ω)^{⊗m}`
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : V.functionField, Ω = c₀ • formPow (f • ω) m := by
    set bL : Module.Basis Unit V.functionField (⋀[V.functionField]^2 Ω[V.functionField⁄k]) :=
      basisOfSpanSingleton (by
        have h1 := span_singleton_topFormsMap (k := k) (K := V.functionField) (d := 2)
          (nonZeroDivisors (V.presheaf.stalk y)) hσ
        rw [hσω] at h1
        rw [← Submodule.span_singleton_smul_eq (IsUnit.mk0 f hf) ω] at h1
        exact h1) hfω0
    refine ⟨(ZTensorPower.basis bL m).repr Ω (), ?_⟩
    have := eq_repr_smul_formPow bL Ω
    rwa [show bL () = f • ω from basisOfSpanSingleton_apply _ _ _] at this
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl; apply hΩ0; rw [hc₀, zero_smul] <;> rfl
  -- `c₀` has order zero along every prime divisor through `y`
  have hc₀ord : ∀ E : Mori.PrimeDivisor V, y ∈ E.support → V.ord c₀ E.genericPoint = 0 := by
    intro E hE
    have h1 := ordForm_smul_formPow (sX := sV) (by rw [hdimV]; rfl) E hfω0 hc₀0 m Ω hc₀
      _ rfl
    have h2 := ordForm_smul_formPow (sX := sV) (by rw [hdimV]; rfl) E hω0 hf 1
      (formPow (f • ω) 1) (by rw [formPow_smul, pow_one]) _ rfl
    have h3 := ordForm_formPow_topFormsMap_eq_zero (sX := sV) hd hσ E hE 1
    rw [hσω] at h3
    rw [h3] at h2
    rw [hord E hE, h2] at h1
    linear_combination -h1
  obtain ⟨c, hcu, hc⟩ := exists_isUnit_algebraMap_eq_of_forall_ord_eq_zero y hc₀0 hc₀ord
  exact ⟨c, hcu, by rw [hc₀, hc]⟩

/-- **Liouville on a smooth proper curve.** Over an algebraically closed field, a rational function
on a smooth proper curve with no zeros or poles is a constant. -/
private theorem exists_eq_algebraMap_of_forall_ord_eq_zero {k : Type} [Field k] [IsAlgClosed k]
    {C : Scheme.{0}} {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    [CompactSpace C] (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    (hdim : topologicalKrullDim C = 1) {f : C.functionField} (hf : f ≠ 0)
    (h : ∀ R : Mori.PrimeDivisor C, C.ord f R.genericPoint = 0) :
    ∃ c : k, letI := functionFieldAlgebra sC; f = algebraMap k _ c := by
  classical
  letI := functionFieldAlgebra sC
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  obtain ⟨x, -, hxc⟩ := (isClosed_univ (X := C)).exists_closed_singleton
    ⟨genericPoint C, trivial⟩
  have hxη : x ≠ genericPoint C := fun h' => not_isClosed_genericPoint hdim (h' ▸ hxc)
  set R₀ : Mori.PrimeDivisor C := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x
    (coheight_eq_one_of_ne_genericPoint hdim hxη)
  have hR₀ : R₀.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  letI := stalkAlgebra sC R₀.genericPoint
  haveI := isScalarTower_stalk_functionField sC R₀.genericPoint
  -- `f` is regular at `R₀`
  obtain ⟨b, hb⟩ : f ∈ (algebraMap R₀.localRing C.functionField).range := by
    rw [← R₀.divisorialValuation_le_one_iff, ← zero_le_ord_iff R₀ hf, h R₀]
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_maximalIdeal sC (hR₀ ▸ hxc) b
  refine ⟨c, ?_⟩
  by_contra hne
  have hne' : f - algebraMap k C.functionField c ≠ 0 := sub_ne_zero.mpr hne
  have hfc : f - algebraMap k C.functionField c =
      algebraMap R₀.localRing C.functionField (b - algebraMap k _ c) := by
    rw [map_sub, hb, ← IsScalarTower.algebraMap_apply]
  have h1 : 1 ≤ C.ord (f - algebraMap k C.functionField c) R₀.genericPoint := by
    rw [hfc]; exact one_le_ord_algebraMap_of_mem R₀ hc (hfc ▸ hne')
  -- constants have order zero
  have hconst : ∀ R : Mori.PrimeDivisor C, algebraMap k C.functionField c = 0 ∨
      0 ≤ C.ord (algebraMap k C.functionField c) R.genericPoint := by
    intro R
    by_cases hc0 : c = 0
    · left; rw [hc0, map_zero]
    · right
      letI := stalkAlgebra sC R.genericPoint
      haveI := isScalarTower_stalk_functionField sC R.genericPoint
      rw [IsScalarTower.algebraMap_apply k (C.presheaf.stalk R.genericPoint) C.functionField]
      exact (MMP.Mori.PrimeDivisor.ord_algebraMap_of_isUnit R
        ((isUnit_iff_ne_zero.2 hc0).map _)).ge
  have h0 : ∀ R : Mori.PrimeDivisor C,
      0 ≤ C.ord (f - algebraMap k C.functionField c) R.genericPoint := fun R =>
    zero_le_ord_sub R hne' (Or.inr (h R).ge) (hconst R)
  -- the degree of a principal divisor vanishes
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero hne'
  have hsum := MMP.Flips.sum_principalDivisor_eq_zero hC hsm hp hdim φ
  have hcoef : ∀ R : Mori.PrimeDivisor C, (MMP.Mori.principalDivisor φ) R =
      C.ord (f - algebraMap k C.functionField c) R.genericPoint := fun R => by
    change DivisorWithCoeffs.coeff (MMP.Mori.principalDivisor φ) R = _
    rw [coeff_principalDivisor, hφ]
  have hmem : R₀ ∈ (MMP.Mori.principalDivisor φ).support := by
    rw [Finsupp.mem_support_iff, hcoef]; omega
  have hle : (MMP.Mori.principalDivisor φ) R₀ ≤ (MMP.Mori.principalDivisor φ).sum
      (fun _ a => a) :=
    Finset.single_le_sum (f := fun R => (MMP.Mori.principalDivisor φ) R)
      (fun R _ => by rw [hcoef]; exact h0 R) hmem
  rw [hsum, hcoef] at hle
  omega

end BisectionB4

section BisectionB5

/-- The reduced closure of the generic point of a prime divisor is cut out by its ideal. -/
private theorem vanishingIdeal_closure_eq_idealSheaf {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] (E : Mori.PrimeDivisor X) {x : X} (hx : x = E.genericPoint) :
    Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure ({x} : Set X)) =
      E.idealSheaf := by
  subst hx
  rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf E]
  congr 1
  apply TopologicalSpace.Closeds.ext
  rw [TopologicalSpace.Closeds.coe_closure]
  exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm

/-- A unit of `𝒪_{X,x}` has order zero along every prime divisor through `x`. -/
private theorem ord_algebraMap_eq_zero_of_isUnit {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (E : Mori.PrimeDivisor X) {x : X} (hx : x ∈ E.support) {a : X.presheaf.stalk x}
    (ha : IsUnit a) : X.ord (algebraMap _ X.functionField a) E.genericPoint = 0 := by
  have hsp := genericPoint_specializes_of_mem_support' E hx
  rw [← MMP.Mori.algebraMap_stalkSpecializes hsp]
  exact E.ord_algebraMap_of_isUnit (ha.map _)

variable {k : Type} [Field k] [IsAlgClosed k]
  {V : Scheme.{0}} {sV : V ⟶ Spec (.of k)} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [CompactSpace V] [LocallyOfFiniteType sV]

/-- **The local ring at a point of a smooth fibre curve.** Let `E` be a prime divisor of a normal
surface lying in the smooth locus, `C` the curve `E`, and `u` a rational function of order one
along `E` and zero along the other prime divisors meeting `E`. At a point `z` of `C` other than
its generic point, `u` is regular, `𝒪_{V, z}` is factorial, and `u` generates the kernel of the
restriction `𝒪_{V,z} → 𝒪_{C,z}`. -/
private theorem exists_fibre_point_data (hdimV : topologicalKrullDim V = 2)
    (E : Mori.PrimeDivisor V) (hEsm : (E.support : Set V) ⊆ Mori.smoothLocus sV)
    (C : ProperCurve sV) (hCE : C.point = E.genericPoint)
    {u : V.functionField} (hu1 : V.ord u E.genericPoint = 1)
    (hu0 : ∀ E' : Mori.PrimeDivisor V, E' ≠ E → ∀ y ∈ E.support, y ∈ E'.support →
      V.ord u E'.genericPoint = 0)
    (z : C.scheme) (hz : z ≠ genericPoint C.scheme) :
    C.ι z ∈ E.support ∧ C.ι z ≠ E.genericPoint ∧ IsClosed ({C.ι z} : Set V) ∧
      UniqueFactorizationMonoid (V.presheaf.stalk (C.ι z)) ∧
      ∃ uy : V.presheaf.stalk (C.ι z), algebraMap _ V.functionField uy = u ∧
        RingHom.ker (C.ι.stalkMap z).hom = Ideal.span {uy} := by
  have hrange : Set.range C.ι.base = (E.support : Set V) := by
    have h : (E.support : Set V) = closure {C.point} := by
      rw [hCE]; exact AlgebraicGeometry.PrimeDivisor.support_eq_closure E
    rw [h]; exact range_curveSubschemeAtι C.point
  have hη : C.ι (genericPoint C.scheme) = E.genericPoint :=
    map_genericPoint_eq_of_range_eq C.ι E hrange
  have hyE : C.ι z ∈ E.support := hrange ▸ ⟨z, rfl⟩
  have hyne : C.ι z ≠ E.genericPoint := fun h =>
    hz (C.ι.isEmbedding.injective (h.trans hη.symm))
  have hyc : IsClosed ({C.ι z} : Set V) := isClosed_singleton_of_mem_support sV hdimV E hyE hyne
  have hreg := isRegularLocalRing_stalk_of_mem_smoothLocus sV (hEsm hyE)
  have hufm : UniqueFactorizationMonoid (V.presheaf.stalk (C.ι z)) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  refine ⟨hyE, hyne, hyc, hufm, ?_⟩
  have hu00 : u ≠ 0 := by rintro rfl; simp at hu1
  obtain ⟨uy, huy⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
    (C.ι z) hu00 fun E' hE' => by
      by_cases h : E' = E
      · subst h; rw [hu1]; norm_num
      · rw [hu0 E' h _ hyE hE']
  obtain ⟨pE, hIE, hpE1, hpE0⟩ := exists_localEquation_of_uniqueFactorizationMonoid E hyE
  have hpE0' : algebraMap _ V.functionField pE ≠ 0 := by
    intro h0; rw [h0] at hpE1; simp at hpE1
  obtain ⟨w, hw, hwu⟩ := exists_isUnit_algebraMap_eq_of_forall_ord_eq_zero (C.ι z)
    (mul_ne_zero hu00 (inv_ne_zero hpE0')) fun E' hE' => by
      rw [Scheme.ord_mul hu00 (inv_ne_zero hpE0'),
        show (algebraMap _ V.functionField pE)⁻¹ = (algebraMap _ V.functionField pE) ^ (-1 : ℤ)
          from (zpow_neg_one _).symm, MMP.Mori.ord_zpow _ hpE0']
      by_cases h : E' = E
      · subst h; rw [hu1, hpE1]; norm_num
      · rw [hu0 E' h _ hyE hE', hpE0 E' hE' h]; norm_num
  have huw : uy = w * pE := by
    apply IsFractionRing.injective (V.presheaf.stalk (C.ι z)) V.functionField
    rw [map_mul, hwu, huy, mul_assoc, inv_mul_cancel₀ hpE0', mul_one]
  refine ⟨uy, huy, ?_⟩
  have hk := Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk
    (Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure ({C.point} : Set V))) z
  have hIx : ∀ x : V, IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({C.point} : Set V))) x =
      IdealSheafData.stalk E.idealSheaf x := fun x => by
    rw [vanishingIdeal_closure_eq_idealSheaf E hCE]
  erw [hk, hIx]
  rw [huw, Ideal.span_singleton_mul_left_unit hw]
  exact hIE

/-- **The residue along a fibre curve of a presented form.** If `Ω = c (p⁻¹ du ∧ db)^{⊗m}` at a
point `y` of `E` with `c` a unit and `p` of order zero along `E`, then the Poincaré residue of
`u^{-m} Ω` along `C` is `ḡ (db̄)^{⊗m}` with `ḡ p̄^m = c̄`. -/
private theorem isPoincareResidue_fibre_of_presentation (E : Mori.PrimeDivisor V) (C : ProperCurve sV)
    (hCE : C.point = E.genericPoint) {u : V.functionField} (hu1 : V.ord u E.genericPoint = 1)
    {y : V} (hsp : C.ι (genericPoint C.scheme) ⤳ y) {uy b c p : V.presheaf.stalk y}
    (huy : letI := stalkAlgebra sV y; letI := functionFieldAlgebra sV
      algebraMap _ V.functionField uy = u)
    (hpE : V.ord (algebraMap _ V.functionField p) E.genericPoint = 0)
    (hp0 : algebraMap _ V.functionField p ≠ 0) {m : ℕ} (Ω : RationalPluriForms sV 2 m)
    (hΩ : letI := stalkAlgebra sV y; letI := functionFieldAlgebra sV
      Ω = (algebraMap _ V.functionField c • formPow ((algebraMap _ V.functionField p)⁻¹ •
        exteriorPower.ιMulti V.functionField 2
          (Fin.cons (KaehlerDifferential.D k V.functionField u)
            fun _ : Fin 1 => KaehlerDifferential.D k V.functionField (algebraMap _ _ b))) m :
        RationalPluriForms sV 2 m)) :
    letI := functionFieldAlgebra sV
    letI := functionFieldAlgebra (C.ι ≫ sV)
    ∃ gbar : C.scheme.functionField,
      gbar * ((C.ι.stalkMap (genericPoint C.scheme)).hom
          ((V.presheaf.stalkSpecializes hsp).hom p)) ^ m =
        (C.ι.stalkMap (genericPoint C.scheme)).hom ((V.presheaf.stalkSpecializes hsp).hom c) ∧
      IsPoincareResidue sV C.ι 1 m ((u⁻¹ ^ m) • Ω)
        (gbar • formPow (exteriorPower.ιMulti C.scheme.functionField 1 fun _ : Fin 1 =>
          KaehlerDifferential.D k C.scheme.functionField ((C.ι.stalkMap (genericPoint C.scheme)).hom
            ((V.presheaf.stalkSpecializes hsp).hom b))) m) := by
  letI := stalkAlgebra sV y
  letI := functionFieldAlgebra sV
  letI := functionFieldAlgebra (C.ι ≫ sV)
  haveI := isScalarTower_stalk_functionField sV y
  have hrange : Set.range C.ι.base = (E.support : Set V) := by
    have h : (E.support : Set V) = closure {C.point} := by
      rw [hCE]; exact AlgebraicGeometry.PrimeDivisor.support_eq_closure E
    rw [h]; exact range_curveSubschemeAtι C.point
  have hη : C.ι (genericPoint C.scheme) = E.genericPoint :=
    map_genericPoint_eq_of_range_eq C.ι E hrange
  have hspalg : ∀ a : V.presheaf.stalk y, algebraMap _ V.functionField
      ((V.presheaf.stalkSpecializes hsp).hom a) = algebraMap _ V.functionField a :=
    MMP.Mori.algebraMap_stalkSpecializes hsp
  have hspu : IsUnit ((V.presheaf.stalkSpecializes hsp).hom p) := by
    have h0 : V.ord (algebraMap _ V.functionField ((V.presheaf.stalkSpecializes hsp).hom p))
        (C.ι (genericPoint C.scheme)) = 0 := by
      rw [hspalg, hη]; exact hpE
    obtain ⟨w, hw, hwe⟩ := exists_isUnit_algebraMap_eq_of_ord_eq_zero
      (by rw [hη]; exact E.coheight_genericPoint) ((hspalg p).symm ▸ hp0) h0
    have : w = (V.presheaf.stalkSpecializes hsp).hom p :=
      IsFractionRing.injective _ V.functionField hwe
    exact this ▸ hw
  set g := (V.presheaf.stalkSpecializes hsp).hom c * ↑(hspu.unit⁻¹) ^ m with hgdef
  have hgF : algebraMap _ V.functionField g =
      algebraMap _ V.functionField c * ((algebraMap _ V.functionField p)⁻¹) ^ m := by
    rw [hgdef, map_mul, map_pow, hspalg, map_units_inv, IsUnit.unit_spec, hspalg]
  have hgp : g * ((V.presheaf.stalkSpecializes hsp).hom p) ^ m =
      (V.presheaf.stalkSpecializes hsp).hom c := by
    rw [hgdef, mul_assoc, ← mul_pow, hspu.val_inv_mul, one_pow, mul_one]
  have hτ : (u⁻¹ ^ m) • Ω = (algebraMap _ V.functionField g • PiTensorProduct.tprod
      V.functionField (fun _ : Fin m => (algebraMap _ V.functionField
        ((V.presheaf.stalkSpecializes hsp).hom uy))⁻¹ •
        exteriorPower.ιMulti V.functionField (1 + 1)
          (Fin.cons (KaehlerDifferential.D k V.functionField
            (algebraMap _ _ ((V.presheaf.stalkSpecializes hsp).hom uy)))
            fun i : Fin 1 => KaehlerDifferential.D k V.functionField
              (algebraMap _ _ ((fun _ : Fin 1 => (V.presheaf.stalkSpecializes hsp).hom b) i)))) :
        TensorPower V.functionField m (⋀[V.functionField]^(1 + 1) Ω[V.functionField⁄k])) := by
    have e1 : algebraMap _ V.functionField ((V.presheaf.stalkSpecializes hsp).hom uy) = u := by
      rw [hspalg, huy]
    simp only [e1, hspalg]
    rw [hgF, hΩ]
    change (u⁻¹ ^ m) • (algebraMap _ V.functionField c • formPow
        ((algebraMap _ V.functionField p)⁻¹ • exteriorPower.ιMulti V.functionField 2
          (Fin.cons (KaehlerDifferential.D k V.functionField u)
            fun _ : Fin 1 => KaehlerDifferential.D k V.functionField (algebraMap _ _ b))) m :
          RationalPluriForms sV 2 m) =
      ((algebraMap _ V.functionField c * ((algebraMap _ V.functionField p)⁻¹) ^ m) • formPow
        (u⁻¹ • exteriorPower.ιMulti V.functionField 2
          (Fin.cons (KaehlerDifferential.D k V.functionField u)
            fun _ : Fin 1 => KaehlerDifferential.D k V.functionField (algebraMap _ _ b))) m :
          RationalPluriForms sV 2 m)
    rw [formPow_smul, formPow_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  refine ⟨(C.ι.stalkMap (genericPoint C.scheme)).hom g, by rw [← map_pow, ← map_mul, hgp],
    ⟨(V.presheaf.stalkSpecializes hsp).hom uy, g,
      fun _ => (V.presheaf.stalkSpecializes hsp).hom b, by rw [hspalg, huy, hη, hu1], hτ, rfl⟩⟩

/-- Generization from a point of the fibre curve to its generic point commutes with restriction to
the curve. -/
private theorem stalkMap_stalkSpecializes_eq_algebraMap (C : ProperCurve sV)
    (z : C.scheme) (hsp : C.ι (genericPoint C.scheme) ⤳ C.ι z) (a : V.presheaf.stalk (C.ι z)) :
    (C.ι.stalkMap (genericPoint C.scheme)).hom ((V.presheaf.stalkSpecializes hsp).hom a) =
      algebraMap (C.scheme.presheaf.stalk z) C.scheme.functionField ((C.ι.stalkMap z).hom a) :=
  C.ι.stalkSpecializes_stalkMap_apply (genericPoint C.scheme) z
    ((genericPoint_spec C.scheme).specializes trivial) a

/-- **The residue along a fibre curve at one of its points.** In the situation of
`exists_fibre_point_data`, let `Ω` be a rational `m`-canonical form with a pole of order `m` along
a prime divisor `P ≠ E` and no zero or pole along the other prime divisors meeting `E`. The
Poincaré residue `ξ` of `u^{-m} Ω` along `C` has order `-m · ord_R(p|_C)` at every point `R` of
`C`, where `p` is a local equation of `P` at `R` (and `p = 1` if `R ∉ P`). -/
private theorem exists_residue_at_fibre_point [CharZero k] (hdimV : topologicalKrullDim V = 2)
    (E : Mori.PrimeDivisor V) (hEsm : (E.support : Set V) ⊆ Mori.smoothLocus sV)
    (C : ProperCurve sV) (hCE : C.point = E.genericPoint)
    {u : V.functionField} (hu1 : V.ord u E.genericPoint = 1)
    (hu0 : ∀ E' : Mori.PrimeDivisor V, E' ≠ E → ∀ y ∈ E.support, y ∈ E'.support →
      V.ord u E'.genericPoint = 0)
    [IsLocallyNoetherian C.scheme] [IsNormal C.scheme] (hZv : IsNormalVariety k (C.ι ≫ sV))
    (hZd : topologicalKrullDim C.scheme = 1) (R : Mori.PrimeDivisor C.scheme)
    (P : Mori.PrimeDivisor V) (hPE : P ≠ E) {m : ℕ} (Ω : RationalPluriForms sV 2 m)
    (hΩ0 : Ω ≠ 0) (hΩP : P.ordForm Ω = -(m : ℤ))
    (hΩ : ∀ E' : Mori.PrimeDivisor V, E' ≠ P → ∀ y ∈ E.support, y ∈ E'.support →
      E'.ordForm Ω = 0) :
    ∃ (p : V.presheaf.stalk (C.ι R.genericPoint)) (ξ : RationalPluriForms (C.ι ≫ sV) 1 m),
      IsPoincareResidue sV C.ι 1 m ((u⁻¹ ^ m) • Ω) ξ ∧ ξ ≠ 0 ∧
      R.ordForm ξ = -(m : ℤ) * C.scheme.ord (algebraMap _ C.scheme.functionField
        ((C.ι.stalkMap R.genericPoint).hom p)) R.genericPoint ∧
      algebraMap _ C.scheme.functionField ((C.ι.stalkMap R.genericPoint).hom p) ≠ 0 ∧
      (C.ι R.genericPoint ∈ P.support →
        V.ord (algebraMap _ V.functionField p) P.genericPoint = 1 ∧
        (∀ E' : Mori.PrimeDivisor V, C.ι R.genericPoint ∈ E'.support → E' ≠ P →
          V.ord (algebraMap _ V.functionField p) E'.genericPoint = 0) ∧
        p ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk (C.ι R.genericPoint))) ∧
      (C.ι R.genericPoint ∉ P.support → p = 1) ∧
      (∀ E' : Mori.PrimeDivisor V, C.ι R.genericPoint ∈ E'.support →
        E'.ordForm Ω = m * V.ord (algebraMap _ V.functionField p)⁻¹ E'.genericPoint) := by
  classical
  letI := functionFieldAlgebra sV
  letI := functionFieldAlgebra (C.ι ≫ sV)
  have : LocallyOfFiniteType (C.ι ≫ sV) := hZv.1.toLocallyOfFiniteType
  set y := C.ι R.genericPoint with hydef
  obtain ⟨hyE, hyne, hyc, hufm, uy, huy, hker⟩ := exists_fibre_point_data hdimV E hEsm C hCE hu1
    hu0 R.genericPoint (PrimeDivisor.genericPoint_ne_genericPoint R)
  letI := stalkAlgebra sV y
  haveI := isScalarTower_stalk_functionField sV y
  have hrange : Set.range C.ι.base = (E.support : Set V) := by
    have h : (E.support : Set V) = closure {C.point} := by
      rw [hCE]; exact AlgebraicGeometry.PrimeDivisor.support_eq_closure E
    rw [h]; exact range_curveSubschemeAtι C.point
  have hη : C.ι (genericPoint C.scheme) = E.genericPoint :=
    map_genericPoint_eq_of_range_eq C.ι E hrange
  have hu00 : u ≠ 0 := by rintro rfl; simp at hu1
  -- the local equation `p` of `P` at `y`, or `1`
  obtain ⟨p, hpP, hp1⟩ : ∃ p : V.presheaf.stalk y,
      (y ∈ P.support → V.ord (algebraMap _ V.functionField p) P.genericPoint = 1 ∧
        (∀ E' : Mori.PrimeDivisor V, y ∈ E'.support → E' ≠ P →
          V.ord (algebraMap _ V.functionField p) E'.genericPoint = 0) ∧
        p ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk y)) ∧ (y ∉ P.support → p = 1) := by
    by_cases hyP : y ∈ P.support
    · obtain ⟨p, -, hp1, hp0⟩ := exists_localEquation_of_uniqueFactorizationMonoid P hyP
      refine ⟨p, fun _ => ⟨hp1, hp0, ?_⟩, fun h => absurd hyP h⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      rw [ord_algebraMap_eq_zero_of_isUnit P hyP hu] at hp1
      exact zero_ne_one hp1
    · exact ⟨1, fun h => absurd h hyP, fun _ => rfl⟩
  have hp0 : algebraMap _ V.functionField p ≠ 0 := by
    by_cases hyP : y ∈ P.support
    · intro h0; have := (hpP hyP).1; rw [h0] at this; simp at this
    · rw [hp1 hyP, map_one]; exact one_ne_zero
  have hpord : ∀ E' : Mori.PrimeDivisor V, y ∈ E'.support → E' ≠ P →
      V.ord (algebraMap _ V.functionField p) E'.genericPoint = 0 := by
    intro E' hE' hne
    by_cases hyP : y ∈ P.support
    · exact (hpP hyP).2.1 E' hE' hne
    · rw [hp1 hyP, map_one]
      exact (Scheme.ord_eq_iff (n := 0) E'.coheight_genericPoint one_ne_zero).2 (by simp)
  -- a uniformizer of `𝒪_{C,R}` and generators of the maximal ideal of `𝒪_{V,y}`
  haveI := R.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R.localRing
  obtain ⟨q, hq⟩ := C.ι.stalkMap_surjective R.genericPoint ϖ
  have hspan : Ideal.span {uy, q} = IsLocalRing.maximalIdeal (V.presheaf.stalk y) :=
    span_pair_eq_maximalIdeal_of_surjective (C.ι.stalkMap R.genericPoint).hom
      (C.ι.stalkMap_surjective R.genericPoint) hker
      (by rw [show (C.ι.stalkMap R.genericPoint).hom q = ϖ from hq]
          exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ)
  -- the presentation `Ω = c (p⁻¹ du ∧ dq)^{⊗m}`
  have hord : ∀ E' : Mori.PrimeDivisor V, y ∈ E'.support →
      E'.ordForm Ω = m * V.ord (algebraMap _ V.functionField p)⁻¹ E'.genericPoint := by
    intro E' hE'
    rw [show (algebraMap _ V.functionField p)⁻¹ = (algebraMap _ V.functionField p) ^ (-1 : ℤ)
      from (zpow_neg_one _).symm, MMP.Mori.ord_zpow _ hp0]
    by_cases hE'P : E' = P
    · subst hE'P; rw [hΩP, (hpP hE').1]; ring
    · rw [hΩ E' hE'P y hyE hE', hpord E' hE' hE'P]; ring
  obtain ⟨c, hcu, hc⟩ := exists_isUnit_smul_formPow_of_span hdimV hyc hspan Ω hΩ0
    (inv_ne_zero hp0) hord
  -- the residue
  have hsp : C.ι (genericPoint C.scheme) ⤳ y := by
    rw [hη]; exact genericPoint_specializes_of_mem_support' E hyE
  rw [huy] at hc
  obtain ⟨gbar, hgbar, hres⟩ := isPoincareResidue_fibre_of_presentation E C hCE hu1 hsp huy
    (hpord E hyE hPE.symm) hp0 Ω hc
  have hnat := stalkMap_stalkSpecializes_eq_algebraMap C R.genericPoint hsp
  set qbar := (C.ι.stalkMap (genericPoint C.scheme)).hom ((V.presheaf.stalkSpecializes hsp).hom q)
    with hqbardef
  set cbar := algebraMap (C.scheme.presheaf.stalk R.genericPoint) C.scheme.functionField
    ((C.ι.stalkMap R.genericPoint).hom c) with hcbardef
  set pbar := algebraMap (C.scheme.presheaf.stalk R.genericPoint) C.scheme.functionField
    ((C.ι.stalkMap R.genericPoint).hom p) with hpbardef
  rw [hnat, hnat] at hgbar
  change gbar * pbar ^ m = cbar at hgbar
  have hqb : C.scheme.ord qbar R.genericPoint = 1 := by
    rw [hqbardef, hnat, show (C.ι.stalkMap R.genericPoint).hom q = ϖ from hq]
    exact (Scheme.ord_eq_iff R.coheight_genericPoint
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero)).mpr
        (Ring.ordFrac_irreducible hϖ)
  obtain ⟨hω0, hωR⟩ := MMP.Flips.ordForm_d_eq_zero hZv hZd R qbar hqb _ rfl
  have hι0 : exteriorPower.ιMulti C.scheme.functionField 1
      (fun _ : Fin 1 => KaehlerDifferential.D k C.scheme.functionField qbar) ≠ 0 := fun h0 =>
    hω0 (by rw [h0]; exact (PiTensorProduct.tprod _).map_coord_zero (0 : Fin 1) rfl)
  have hcb : C.scheme.ord cbar R.genericPoint = 0 :=
    R.ord_algebraMap_of_isUnit (hcu.map (C.ι.stalkMap R.genericPoint).hom)
  have hcb0 : cbar ≠ 0 := ((hcu.map (C.ι.stalkMap R.genericPoint).hom).map _).ne_zero
  have hg0 : gbar ≠ 0 := by
    rintro h0; rw [h0, zero_mul] at hgbar; exact hcb0 hgbar.symm
  have hpb0 : pbar ≠ 0 := by
    intro h0
    have h1 : (C.ι.stalkMap R.genericPoint).hom p = 0 :=
      IsFractionRing.injective _ C.scheme.functionField (by rw [← hpbardef, h0, map_zero])
    have h2 : p ∈ RingHom.ker (C.ι.stalkMap R.genericPoint).hom := h1
    rw [hker, Ideal.mem_span_singleton'] at h2
    obtain ⟨r, hr⟩ := h2
    have h3 := hpord E hyE hPE.symm
    rw [← hr, map_mul, huy] at h3
    have hr0 : algebraMap _ V.functionField r ≠ 0 := by
      intro h; rw [← hr, map_mul, h, zero_mul] at hp0; exact hp0 rfl
    rw [Scheme.ord_mul hr0 hu00, hu1] at h3
    have h4 : 0 ≤ V.ord (algebraMap _ V.functionField r) E.genericPoint := by
      rw [← MMP.Mori.algebraMap_stalkSpecializes (genericPoint_specializes_of_mem_support' E hyE)]
      exact zero_le_ord_algebraMap_localRing E
        (by rwa [MMP.Mori.algebraMap_stalkSpecializes])
    omega
  refine ⟨p, _, hres, smul_ne_zero hg0 (formPow_ne_zero_of_ne_zero (sX := C.ι ≫ sV) hZd hι0 m),
    ?_, hpb0, fun h => hpP h, fun h => hp1 h, hord⟩
  have h1 := ordForm_smul_formPow (sX := C.ι ≫ sV) (d := 1) (by rw [hZd]; rfl) R hι0 hg0 m
    _ rfl _ rfl
  rw [h1]
  erw [hωR]
  have h2 : C.scheme.ord gbar R.genericPoint + m * C.scheme.ord pbar R.genericPoint = 0 := by
    rw [← hcb, ← hgbar, Scheme.ord_mul hg0 (pow_ne_zero _ hpb0),
      show pbar ^ m = pbar ^ (m : ℤ) from (zpow_natCast _ _).symm, MMP.Mori.ord_zpow _ hpb0]
  linear_combination h2

end BisectionB5

section BisectionB6

/-- An element of order one of the local ring at a prime divisor generates its maximal ideal. -/
private theorem maximalIdeal_eq_span_of_ord_eq_one {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (R : Mori.PrimeDivisor X) {a : R.localRing}
    (ha : X.ord (algebraMap R.localRing X.functionField a) R.genericPoint = 1) :
    IsLocalRing.maximalIdeal R.localRing = Ideal.span {a} := by
  haveI := R.isDiscreteValuationRing_localRing
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R.localRing
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  have hϖ0 : algebraMap R.localRing X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  have hϖ1 : X.ord (algebraMap R.localRing X.functionField ϖ) R.genericPoint = 1 :=
    (Scheme.ord_eq_iff R.coheight_genericPoint hϖ0).mpr (Ring.ordFrac_irreducible hϖ)
  have hv0 : algebraMap R.localRing X.functionField v ≠ 0 := (v.isUnit.map _).ne_zero
  rw [map_mul, map_pow, Scheme.ord_mul hv0 (pow_ne_zero _ hϖ0),
    R.ord_algebraMap_of_isUnit v.isUnit, zero_add,
    show (algebraMap R.localRing X.functionField ϖ) ^ n =
      (algebraMap R.localRing X.functionField ϖ) ^ (n : ℤ) from (zpow_natCast _ _).symm,
    MMP.Mori.ord_zpow _ hϖ0, hϖ1, mul_one] at ha
  have hn : n = 1 := by exact_mod_cast ha
  subst hn
  rw [pow_one]
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp
    ((irreducible_units_mul v).mpr hϖ)

/-- Stalk maps of schemes over `k` are `k`-linear. -/
private theorem stalkMap_algebraMap {k : Type} [Field k] {Y T : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    (j : T ⟶ Y) (x : T) (c : k) :
    letI := stalkAlgebra sY (j x)
    letI := stalkAlgebra (j ≫ sY) x
    (j.stalkMap x).hom (algebraMap k _ c) = algebraMap k _ c := by
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ sY).appTop ≫
        T.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫
        Y.presheaf.germ ⊤ (j x) (TopologicalSpace.Opens.mem_top _)) ≫ j.stalkMap x := by
    simp only [Category.assoc, Scheme.Hom.germ_stalkMap, Scheme.Hom.comp_appTop]
    rfl
  exact (congrArg (fun f => (CommRingCat.Hom.hom f) c) h).symm

/-- `ιMulti` of a pair changes sign under the swap. -/
private theorem ιMulti_cons_swap {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a b : M) :
    exteriorPower.ιMulti R 2 (Fin.cons a fun _ : Fin 1 => b) =
      -exteriorPower.ιMulti R 2 (Fin.cons b fun _ : Fin 1 => a) := by
  have hsw : (Fin.cons a fun _ : Fin 1 => b : Fin 2 → M) =
      (Fin.cons b fun _ : Fin 1 => a : Fin 2 → M) ∘ Equiv.swap (0 : Fin 2) 1 := by
    ext i; fin_cases i <;> rfl
  rw [hsw]
  exact eq_neg_of_add_eq_zero_left
    ((exteriorPower.ιMulti R 2).map_swap_add _ (by decide : (0 : Fin 2) ≠ 1))

/-- For `m` even, `(-ω)^{⊗m} = ω^{⊗m}`. -/
private theorem formPow_neg_of_even {k K : Type*} [CommRing k] [Field K] [Algebra k K] {d : ℕ}
    (ω : ⋀[K]^d Ω[K⁄k]) {m : ℕ} (hm : Even m) : formPow (-ω) m = formPow ω m := by
  rw [← neg_one_smul K ω, formPow_smul, hm.neg_one_pow, one_smul]

/-- In a line, `x = (x/y) • y` for `y ≠ 0`, the ratio taken in coordinates. -/
private theorem eq_div_repr_smul {k K : Type*} [CommRing k] [Field K] [Algebra k K] {d : ℕ}
    (b : Module.Basis Unit K (⋀[K]^d Ω[K⁄k])) {m : ℕ} (x y : PluriForms k K d m)
    (hy : (ZTensorPower.basis b m).repr y () ≠ 0) :
    x = ((ZTensorPower.basis b m).repr x () / (ZTensorPower.basis b m).repr y ()) • y := by
  calc x = (ZTensorPower.basis b m).repr x () • formPow (b ()) m := eq_repr_smul_formPow b x
    _ = ((ZTensorPower.basis b m).repr x () / (ZTensorPower.basis b m).repr y ()) •
        ((ZTensorPower.basis b m).repr y () • formPow (b ()) m) := by
      rw [smul_smul, div_mul_cancel₀ _ hy]
    _ = _ := by rw [← eq_repr_smul_formPow b y]

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
  {V : Scheme.{0}} {sV : V ⟶ Spec (.of k)} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [CompactSpace V] [LocallyOfFiniteType sV]

/-- **Leading coefficients at a transversal point.** On the fibre curve `C`, let
`ξ = c₀ (dw/w)^{⊗m}` and let `p` be a local parameter at `R`. If `ξ = c (dp/p)^{⊗m}` near `R`,
with `c` in the local ring of the surface, and `(dw'/w')^{⊗m} = (dw/w)^{⊗m}` for a local parameter
`w'` at `R`, then `c ≡ c₀` modulo the maximal ideal. -/
private theorem sub_algebraMap_mem_maximalIdeal_of_residue (C : ProperCurve sV)
    [IsLocallyNoetherian C.scheme] [IsNormal C.scheme] (hZv : IsNormalVariety k (C.ι ≫ sV))
    (hZd : topologicalKrullDim C.scheme = 1) {m : ℕ} {ξ : RationalPluriForms (C.ι ≫ sV) 1 m}
    {w f₀ : C.scheme.functionField} (hf₀ : ξ = f₀ • MMP.Flips.dlogPow (C.ι ≫ sV) w m) {c₀ : k}
    (hc₀ : letI := functionFieldAlgebra (C.ι ≫ sV); f₀ = algebraMap k _ c₀)
    (R : Mori.PrimeDivisor C.scheme) (p c : V.presheaf.stalk (C.ι R.genericPoint))
    (w' : C.scheme.functionField) (hw' : C.scheme.ord w' R.genericPoint = 1)
    (hww : MMP.Flips.dlogPow (C.ι ≫ sV) w' m = MMP.Flips.dlogPow (C.ι ≫ sV) w m)
    (hiR1 : C.scheme.ord (algebraMap _ C.scheme.functionField
      ((C.ι.stalkMap R.genericPoint).hom p)) R.genericPoint = 1)
    (hξc : ξ = algebraMap _ C.scheme.functionField ((C.ι.stalkMap R.genericPoint).hom c) •
      MMP.Flips.dlogPow (C.ι ≫ sV) (algebraMap _ C.scheme.functionField
        ((C.ι.stalkMap R.genericPoint).hom p)) m) :
    letI := stalkAlgebra sV (C.ι R.genericPoint)
    c - algebraMap k _ c₀ ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk (C.ι R.genericPoint)) := by
  letI := functionFieldAlgebra (C.ι ≫ sV)
  letI := stalkAlgebra sV (C.ι R.genericPoint)
  letI := stalkAlgebra (C.ι ≫ sV) R.genericPoint
  haveI := isScalarTower_stalk_functionField (C.ι ≫ sV) R.genericPoint
  set pb := algebraMap _ C.scheme.functionField ((C.ι.stalkMap R.genericPoint).hom p)
  obtain ⟨h, hh1, hhw⟩ := exists_dlogPow_eq_pow_smul hZv hZd R hw' hiR1 m
  obtain ⟨hpb0', -⟩ := MMP.Flips.ordForm_dlogPow_one_of_ord_eq_one hZv hZd R pb hiR1
  obtain ⟨hpbm0, -⟩ := MMP.Flips.ordForm_dlogPow_eq_mul hZv hZd pb hpb0' m
  have heq : algebraMap _ C.scheme.functionField ((C.ι.stalkMap R.genericPoint).hom c) =
      algebraMap k C.scheme.functionField c₀ * h ^ m := by
    apply smul_left_injective C.scheme.functionField hpbm0
    change _ • _ = _ • _
    rw [← hξc, hf₀, hc₀, ← hww, hhw, smul_smul]
  have hdiff : algebraMap _ C.scheme.functionField ((C.ι.stalkMap R.genericPoint).hom
      (c - algebraMap k _ c₀)) = algebraMap k C.scheme.functionField c₀ * (h ^ m - 1) := by
    rw [map_sub, map_sub, heq, stalkMap_algebraMap sV C.ι R.genericPoint c₀,
      ← IsScalarTower.algebraMap_apply]
    ring
  have hconst : algebraMap k C.scheme.functionField c₀ = 0 ∨
      C.scheme.ord (algebraMap k C.scheme.functionField c₀) R.genericPoint = 0 := by
    by_cases hc0 : c₀ = 0
    · left; rw [hc0, map_zero]
    · right
      rw [IsScalarTower.algebraMap_apply k (C.scheme.presheaf.stalk R.genericPoint)
        C.scheme.functionField]
      exact R.ord_algebraMap_of_isUnit ((isUnit_iff_ne_zero.2 hc0).map _)
  have hpos := one_le_ord_mul_of_ord_eq_zero R hconst (one_le_ord_pow_sub_one R hh1 m)
  rw [← hdiff] at hpos
  -- the image of `c - c₀` lies in the maximal ideal of `𝒪_{C,R}`, hence so does `c - c₀`
  have hmz : (C.ι.stalkMap R.genericPoint).hom (c - algebraMap k _ c₀) ∈
      IsLocalRing.maximalIdeal R.localRing := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rcases hpos with h0 | h0
    · exact (hu.map (algebraMap R.localRing C.scheme.functionField)).ne_zero h0
    · rw [R.ord_algebraMap_of_isUnit hu] at h0; exact absurd h0 (by norm_num)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmz ⊢
  exact fun hu => hmz (hu.map _)

/-- **The residues of a form along two points of a fibre.** Let `E` be a smooth fibre of a normal
surface, `C ≅ ℙ¹` the curve `E`, `u` a rational function of order one along `E` and zero along the
other prime divisors meeting `E`, and `Ω` a rational `m`-canonical form, `m` even, with a pole of
order `m` along a prime divisor `P ≠ E` and no zero or pole along the other prime divisors
meeting `E`. If `P` meets `E` in two points `y₁ ≠ y₂`, then at both points
`Ω = c (p⁻¹ dp ∧ du)^{⊗m}`, with `p` a local equation of `P` and `c` a unit, and `c` takes the
same value `c₀ ∈ k` at `y₁` and at `y₂`. -/
private theorem exists_const_of_fibre (hdimV : topologicalKrullDim V = 2)
    (E : Mori.PrimeDivisor V) (hEsm : (E.support : Set V) ⊆ Mori.smoothLocus sV)
    (C : ProperCurve sV) (hCE : C.point = E.genericPoint)
    (e : projectiveLine k ≅ C.scheme) (he : e.hom ≫ C.ι ≫ sV = projectiveLine k ↘ Spec (.of k))
    {u : V.functionField} (hu1 : V.ord u E.genericPoint = 1)
    (hu0 : ∀ E' : Mori.PrimeDivisor V, E' ≠ E → ∀ y ∈ E.support, y ∈ E'.support →
      V.ord u E'.genericPoint = 0)
    (P : Mori.PrimeDivisor V) (hPE : P ≠ E)
    {m : ℕ} (hm : 0 < m) (hme : Even m) (Ω : RationalPluriForms sV 2 m) (hΩ0 : Ω ≠ 0)
    (hΩP : P.ordForm Ω = -(m : ℤ))
    (hΩ : ∀ E' : Mori.PrimeDivisor V, E' ≠ P → ∀ y ∈ E.support, y ∈ E'.support →
      E'.ordForm Ω = 0)
    {y₁ y₂ : V} (hy₁P : y₁ ∈ P.support) (hy₁E : y₁ ∈ E.support)
    (hy₂P : y₂ ∈ P.support) (hy₂E : y₂ ∈ E.support) (hne : y₁ ≠ y₂) :
    ∃ c₀ : k, ∀ y : V, (y = y₁ ∨ y = y₂) →
      letI := stalkAlgebra sV y
      letI := functionFieldAlgebra sV
      ∃ p c uy : V.presheaf.stalk y, algebraMap _ V.functionField uy = u ∧
        V.ord (algebraMap _ V.functionField p) P.genericPoint = 1 ∧ IsUnit c ∧
        c - algebraMap k _ c₀ ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk y) ∧
        Ω = (algebraMap _ V.functionField c • formPow ((algebraMap _ V.functionField p)⁻¹ •
          exteriorPower.ιMulti V.functionField 2
            (Fin.cons (KaehlerDifferential.D k V.functionField (algebraMap _ _ p))
              fun _ : Fin 1 => KaehlerDifferential.D k V.functionField u)) m :
          RationalPluriForms sV 2 m) := by
  classical
  letI := functionFieldAlgebra sV
  -- the fibre curve is a smooth rational curve
  obtain ⟨hZsm, hZn, hZp, hZd, hZc⟩ := smooth_isNormal_of_iso_projectiveLine (C.ι ≫ sV) e he
  haveI := hZn
  haveI := hZp
  haveI : LocallyOfFiniteType (C.ι ≫ sV) := inferInstance
  haveI : IsLocallyNoetherian C.scheme := LocallyOfFiniteType.isLocallyNoetherian (C.ι ≫ sV)
  haveI : CompactSpace C.scheme := QuasiCompact.compactSpace_of_compactSpace (C.ι ≫ sV)
  have hZv : IsNormalVariety k (C.ι ≫ sV) := ⟨hZc.toIsVariety, hZn⟩
  have hZs : IsSmoothScheme (C.ι ≫ sV) := MMP.Mori.isSmoothScheme_of_smooth hZsm
  have hd1 : topologicalKrullDim C.scheme = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hZd
  obtain ⟨KZ, hKZ⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (C.ι ≫ sV) hZv
    (n := 1) (by rw [hZd]; rfl)
  have hgZ := h0_canonical_eq_zero_of_iso_projectiveLine (C.ι ≫ sV) e he hZv hKZ
  letI := functionFieldAlgebra (C.ι ≫ sV)
  have hrange : Set.range C.ι.base = (E.support : Set V) := by
    have h : (E.support : Set V) = closure {C.point} := by
      rw [hCE]; exact AlgebraicGeometry.PrimeDivisor.support_eq_closure E
    rw [h]; exact range_curveSubschemeAtι C.point
  have hη : C.ι (genericPoint C.scheme) = E.genericPoint :=
    map_genericPoint_eq_of_range_eq C.ι E hrange
  -- the points of `C` over `y₁, y₂`
  have hpt : ∀ y ∈ E.support, y ∈ P.support →
      ∃ R : Mori.PrimeDivisor C.scheme, C.ι R.genericPoint = y := by
    intro y hyE hyP
    obtain ⟨z, rfl⟩ : y ∈ Set.range C.ι.base := hrange ▸ hyE
    have hzη : z ≠ genericPoint C.scheme := by
      rintro rfl
      exact hPE (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support P E (hη ▸ hyP))
    exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne z
      (coheight_eq_one_of_ne_genericPoint hZd hzη), congrArg (fun w => C.ι w)
        (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z
          (coheight_eq_one_of_ne_genericPoint hZd hzη))⟩
  obtain ⟨R₁, rfl⟩ := hpt y₁ hy₁E hy₁P
  obtain ⟨R₂, rfl⟩ := hpt y₂ hy₂E hy₂P
  have hR : R₁ ≠ R₂ := fun h => hne (by rw [h])
  -- the residue `ξ` of `u^{-m} Ω` along `C` and its orders
  choose pR ξR hξR hξ0 hordR hpbar0 hPR hnPR hordΩ using fun R : Mori.PrimeDivisor C.scheme =>
    exists_residue_at_fibre_point hdimV E hEsm C hCE hu1 hu0 hZv hZd R P hPE Ω hΩ0 hΩP hΩ
  set ξ := ξR R₁ with hξdef
  have hξ : ∀ R, ξR R = ξ := fun R =>
    IsPoincareResidue.unique_of_isClosedImmersion E hη (hξR R) (hξR R₁)
  set i : Mori.PrimeDivisor C.scheme → ℤ := fun R => C.scheme.ord
    (algebraMap _ C.scheme.functionField ((C.ι.stalkMap R.genericPoint).hom (pR R)))
    R.genericPoint with hidef
  have hi0 : ∀ R, 0 ≤ i R := fun R => zero_le_ord_algebraMap_localRing R (hpbar0 R)
  have hi1 : ∀ R, C.ι R.genericPoint ∈ P.support → 1 ≤ i R := fun R hRP =>
    one_le_ord_algebraMap_of_mem R ((IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp (hPR R hRP).2.2 ((isUnit_map_iff _ _).mp hu))
      (hpbar0 R)
  have hordξ : ∀ R, R.ordForm ξ = -(m : ℤ) * i R := fun R => by
    rw [← hξ R]; exact hordR R
  -- the degree of `ξ` forces transversality at `R₁, R₂` and no other pole
  have hsum := sum_divisorOfForm_eq_of_genus_zero hZv hZs hZp hZd hKZ hgZ (hξ0 R₁)
  rw [← hξdef] at hsum
  have hD : ∀ R, divisorOfForm ξ R = -(m : ℤ) * i R := fun R => hordξ R
  have hmem : ∀ R, 1 ≤ i R → R ∈ (divisorOfForm ξ).support := fun R h => by
    rw [Finsupp.mem_support_iff, hD]
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    exact mul_ne_zero (by omega) (by omega)
  have hle : ∀ t : Finset (Mori.PrimeDivisor C.scheme), t ⊆ (divisorOfForm ξ).support →
      ∑ R ∈ t, (m : ℤ) * i R ≤ 2 * m := by
    intro t ht
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg ht (f := fun R => (m : ℤ) * i R)
      (fun R _ _ => mul_nonneg (by positivity) (hi0 R))
    have h2 : ∑ R ∈ (divisorOfForm ξ).support, (m : ℤ) * i R = 2 * m := by
      have : (divisorOfForm ξ).sum (fun _ a => a) = ∑ R ∈ (divisorOfForm ξ).support,
          -((m : ℤ) * i R) := by
        simp only [Finsupp.sum, hD, neg_mul]
      rw [this, Finset.sum_neg_distrib] at hsum
      linarith
    linarith
  have hiR₁ : i R₁ = 1 ∧ i R₂ = 1 := by
    have h := hle {R₁, R₂} (by
      intro R hR'
      rcases Finset.mem_insert.mp hR' with rfl | h
      · exact hmem _ (hi1 _ hy₁P)
      · rw [Finset.mem_singleton] at h; subst h; exact hmem _ (hi1 _ hy₂P))
    rw [Finset.sum_pair hR] at h
    have h1 := hi1 _ hy₁P
    have h2 := hi1 _ hy₂P
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    constructor <;> nlinarith
  have hiR : ∀ R, i R = (if R = R₁ then 1 else 0) + (if R = R₂ then 1 else 0) := by
    intro R
    by_cases h1 : R = R₁
    · subst h1; simp [hR, hiR₁.1]
    by_cases h2 : R = R₂
    · subst h2; simp [Ne.symm hR, hiR₁.2]
    simp only [if_neg h1, if_neg h2, add_zero]
    by_contra hne0
    have hpos : 1 ≤ i R := by have := hi0 R; omega
    have h := hle {R, R₁, R₂} (by
      intro R' hR'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR'
      rcases hR' with rfl | rfl | rfl
      · exact hmem _ hpos
      · exact hmem _ (hi1 _ hy₁P)
      · exact hmem _ (hi1 _ hy₂P))
    rw [Finset.sum_insert (by simp [h1, h2]), Finset.sum_pair hR, hiR₁.1, hiR₁.2] at h
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    nlinarith
  -- presentations at the two transversal points
  have hpres : ∀ R : Mori.PrimeDivisor C.scheme, C.ι R.genericPoint ∈ P.support → i R = 1 →
      letI := stalkAlgebra sV (C.ι R.genericPoint)
      ∃ c uy : V.presheaf.stalk (C.ι R.genericPoint), algebraMap _ V.functionField uy = u ∧
        IsUnit c ∧
        Ω = (algebraMap _ V.functionField c • formPow
          ((algebraMap _ V.functionField (pR R))⁻¹ • exteriorPower.ιMulti V.functionField 2
            (Fin.cons (KaehlerDifferential.D k V.functionField (algebraMap _ _ (pR R)))
              fun _ : Fin 1 => KaehlerDifferential.D k V.functionField u)) m :
          RationalPluriForms sV 2 m) ∧
        ξ = algebraMap _ C.scheme.functionField ((C.ι.stalkMap R.genericPoint).hom c) •
          MMP.Flips.dlogPow (C.ι ≫ sV) (algebraMap _ C.scheme.functionField
            ((C.ι.stalkMap R.genericPoint).hom (pR R))) m := by
    intro R hRP hiR1
    obtain ⟨hyE, hyne, hyc, hufm, uy, huy, hker⟩ := exists_fibre_point_data hdimV E hEsm C hCE
      hu1 hu0 R.genericPoint (PrimeDivisor.genericPoint_ne_genericPoint R)
    letI := stalkAlgebra sV (C.ι R.genericPoint)
    haveI := isScalarTower_stalk_functionField sV (C.ι R.genericPoint)
    have hmz : IsLocalRing.maximalIdeal R.localRing =
        Ideal.span {(C.ι.stalkMap R.genericPoint).hom (pR R)} :=
      maximalIdeal_eq_span_of_ord_eq_one R hiR1
    have hspan : Ideal.span {pR R, uy} = IsLocalRing.maximalIdeal _ := by
      rw [Set.pair_comm]
      exact span_pair_eq_maximalIdeal_of_surjective _ (C.ι.stalkMap_surjective R.genericPoint)
        hker hmz
    have hp0 : algebraMap _ V.functionField (pR R) ≠ 0 := by
      intro h0; have := (hPR R hRP).1; rw [h0] at this; simp at this
    obtain ⟨c, hcu, hc⟩ := exists_isUnit_smul_formPow_of_span hdimV hyc hspan Ω hΩ0
      (inv_ne_zero hp0) (hordΩ R)
    rw [huy] at hc
    refine ⟨c, uy, huy, hcu, hc, ?_⟩
    have hc' : Ω = (algebraMap _ V.functionField c • formPow
        ((algebraMap _ V.functionField (pR R))⁻¹ • exteriorPower.ιMulti V.functionField 2
          (Fin.cons (KaehlerDifferential.D k V.functionField u)
            fun _ : Fin 1 => KaehlerDifferential.D k V.functionField (algebraMap _ _ (pR R)))) m :
          RationalPluriForms sV 2 m) := by
      rw [hc, ιMulti_cons_swap, smul_neg, formPow_neg_of_even _ hme]
    have hsp : C.ι (genericPoint C.scheme) ⤳ C.ι R.genericPoint := by
      rw [hη]; exact genericPoint_specializes_of_mem_support' E hyE
    obtain ⟨gbar, hgbar, hres⟩ := isPoincareResidue_fibre_of_presentation E C hCE hu1 hsp huy
      ((hPR R hRP).2.1 E hyE hPE.symm) hp0 Ω hc'
    have hnat := stalkMap_stalkSpecializes_eq_algebraMap C R.genericPoint hsp
    rw [hnat, hnat] at hgbar
    have hξ' := IsPoincareResidue.unique_of_isClosedImmersion E hη hres (hξR R₁)
    rw [← hξdef] at hξ'
    rw [← hξ', hnat]
    set pb := algebraMap _ C.scheme.functionField ((C.ι.stalkMap R.genericPoint).hom (pR R))
      with hpbdef
    have hgb : gbar = algebraMap _ C.scheme.functionField
        ((C.ι.stalkMap R.genericPoint).hom c) * (pb⁻¹) ^ m := by
      rw [← hgbar, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (hpbar0 R)), mul_one]
    rw [hgb]
    unfold MMP.Flips.dlogPow formPow
    simp only
    rw [tprod_const_smul]
    exact mul_smul _ _ _
  obtain ⟨c₁, uy₁, huy₁, hc₁u, hΩ₁, hξ₁⟩ := hpres R₁ hy₁P hiR₁.1
  obtain ⟨c₂, uy₂, huy₂, hc₂u, hΩ₂, hξ₂⟩ := hpres R₂ hy₂P hiR₁.2
  -- the rational function `w` with divisor `R₁ - R₂`
  have hsumhom : ∀ D : Divisor C.scheme, (D.sum fun _ a => a) =
      Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ) D :=
    fun D => by rw [Finsupp.liftAddHom_apply]; rfl
  obtain ⟨φ, hφ⟩ := MMP.Flips.exists_principalDivisor_add_eq_zero hZv hZs hZp hZd hKZ hgZ
    (Finsupp.single R₂ 1 - Finsupp.single R₁ 1) (by
      rw [hsumhom, map_sub, Finsupp.liftAddHom_apply_single, Finsupp.liftAddHom_apply_single]
      rfl)
  obtain ⟨w, hw0, hwφ⟩ := MMP.Positivity.exists_ord_eq_of_units φ
  have hw : ∀ R : Mori.PrimeDivisor C.scheme, C.scheme.ord w R.genericPoint =
      (if R = R₁ then 1 else 0) - (if R = R₂ then 1 else 0) := by
    intro R
    have h := congrArg (fun D : Divisor C.scheme => D R) hφ
    simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.coe_zero,
      Pi.zero_apply] at h
    have h' : (MMP.Mori.principalDivisor φ) R = R.ord φ := by
      change DivisorWithCoeffs.coeff (MMP.Mori.principalDivisor φ) R = _
      rw [coeff_principalDivisor]
    rw [← hwφ, ← h']
    by_cases h1 : R = R₁
    · subst h1; simp [hR, Ne.symm hR] at h ⊢; omega
    · by_cases h2 : R = R₂
      · subst h2; simp [h1, Ne.symm h1] at h ⊢; omega
      · simp [h1, h2, Ne.symm h1, Ne.symm h2] at h ⊢; omega
  obtain ⟨hdl0, hdl⟩ := MMP.Flips.ordForm_dlogPow_of_ord hZv hZs hZp hZd hKZ hgZ hR w hw0 hw m
  -- `ξ` is a constant multiple of `(dw/w)^{⊗m}`
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hZv (n := 1) hd1
  have hline : ∀ x y : RationalPluriForms (C.ι ≫ sV) 1 m,
      (ZTensorPower.basis b m).repr y () ≠ 0 →
      x = ((ZTensorPower.basis b m).repr x () / (ZTensorPower.basis b m).repr y ()) • y :=
    fun x y hy => eq_div_repr_smul b x y hy
  have hrw0 : (ZTensorPower.basis b m).repr (MMP.Flips.dlogPow (C.ι ≫ sV) w m) () ≠ 0 :=
    MMP.Mori.repr_ne_zero_of_ne_zero b hdl0
  set f₀ := (ZTensorPower.basis b m).repr ξ () /
    (ZTensorPower.basis b m).repr (MMP.Flips.dlogPow (C.ι ≫ sV) w m) () with hf₀def
  have hf₀ : ξ = f₀ • MMP.Flips.dlogPow (C.ι ≫ sV) w m := hline _ _ hrw0
  have hf₀0 : f₀ ≠ 0 := by
    rintro h0; apply hξ0 R₁; rw [← hξdef, hf₀, h0, zero_smul]
  have hf₀ord : ∀ R : Mori.PrimeDivisor C.scheme, C.scheme.ord f₀ R.genericPoint = 0 := by
    intro R
    have h1 := R.ordForm_smul_of_topologicalKrullDim_eq hd1 hf₀0 hdl0
    rw [← hf₀, hordξ, hdl R, hiR R] at h1
    linarith
  obtain ⟨c₀, hc₀⟩ := exists_eq_algebraMap_of_forall_ord_eq_zero hZv hZs hZp hZd hf₀0 hf₀ord
  -- comparison of leading coefficients at a transversal point
  have hval : ∀ (R : Mori.PrimeDivisor C.scheme) (c : V.presheaf.stalk (C.ι R.genericPoint))
      (w' : C.scheme.functionField), C.scheme.ord w' R.genericPoint = 1 →
      MMP.Flips.dlogPow (C.ι ≫ sV) w' m = MMP.Flips.dlogPow (C.ι ≫ sV) w m → i R = 1 →
      ξ = algebraMap _ C.scheme.functionField ((C.ι.stalkMap R.genericPoint).hom c) •
        MMP.Flips.dlogPow (C.ι ≫ sV) (algebraMap _ C.scheme.functionField
          ((C.ι.stalkMap R.genericPoint).hom (pR R))) m →
      letI := stalkAlgebra sV (C.ι R.genericPoint)
      c - algebraMap k _ c₀ ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk (C.ι R.genericPoint)) :=
    fun R c w' hw' hww hiR1 hξc =>
      sub_algebraMap_mem_maximalIdeal_of_residue C hZv hZd hf₀ hc₀ R (pR R) c w' hw' hww hiR1 hξc
  refine ⟨c₀, fun y hy => ?_⟩
  rcases hy with rfl | rfl
  · exact ⟨pR R₁, c₁, uy₁, huy₁, (hPR R₁ hy₁P).1, hc₁u,
      hval R₁ c₁ w (by rw [hw]; simp [hR]) rfl hiR₁.1 hξ₁, hΩ₁⟩
  · refine ⟨pR R₂, c₂, uy₂, huy₂, (hPR R₂ hy₂P).1, hc₂u,
      hval R₂ c₂ w⁻¹ ?_ (MMP.Flips.dlogPow_inv _ w hw0 hme) hiR₁.2 hξ₂, hΩ₂⟩
    rw [show w⁻¹ = w ^ (-1 : ℤ) from (zpow_neg_one w).symm, MMP.Mori.ord_zpow _ hw0, hw]
    simp [Ne.symm hR]

end BisectionB6

section BisectionB7

open MMP.Fourfold.SNCWeight.SNCModel (Dominates exists_dominates_of_isProper)

variable {N T : Scheme.{0}} [IsIntegral N] [IsLocallyNoetherian N] [IsNormal N] [IsIntegral T]

/-- **Centres of transported valuations.** Let `φ : N ⟶ T` be proper and dominant and `σ` an
automorphism of `k(N)` over `k(T)`. For every prime divisor `Q` of `N`, the valuation `v_Q ∘ σ`
has a centre `x'` on `N` lying over the image of `Q`. -/
private theorem exists_dominates_comap {k : Type} [Field k] {sN : N ⟶ Spec (.of k)} (φ : N ⟶ T)
    [IsProper φ] [IsDominant φ] (σ : FunctionFieldEquiv sN sN)
    (hσ : ∀ a, σ (functionFieldMap φ a) = functionFieldMap φ a) (Q : Mori.PrimeDivisor N) :
    letI := functionFieldAlgebra sN
    ∃ x' : N, Dominates (Q.divisorialValuation.comap σ.toRingEquiv.toRingHom) x' ∧
      φ x' = φ Q.genericPoint := by
  letI := functionFieldAlgebra sN
  refine exists_dominates_of_isProper φ _ (φ Q.genericPoint) ⟨fun a => ?_, fun a ha => ?_⟩
  · rw [Valuation.comap_apply, Valuation.comap_apply]
    change Q.divisorialValuation (σ (functionFieldMap φ _)) ≤ 1
    rw [hσ, MMP.Mori.functionFieldMap_algebraMap_stalk φ Q.genericPoint a]
    exact (Q.divisorialValuation_le_one_iff _).mpr ⟨_, rfl⟩
  · rw [Valuation.comap_apply, Valuation.comap_apply]
    change Q.divisorialValuation (σ (functionFieldMap φ _)) < 1
    rw [hσ, MMP.Mori.functionFieldMap_algebraMap_stalk φ Q.genericPoint a]
    refine (Q.divisorialValuation_algebraMap_lt_one_iff _).mpr ?_
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp ha ((isUnit_map_iff _ a).mp hu)

/-- **Values transfer along a morphism.** If `a ≡ b` modulo the maximal ideal of `𝒪_{V,ν x}`,
then their generizations restricted to `k(N)` differ by the image of an element of the maximal
ideal of `𝒪_{N,x}`. -/
private theorem exists_mem_maximalIdeal_of_sub_mem {V : Scheme.{0}} (ν : N ⟶ V) (x : N)
    (hsp : ν (genericPoint N) ⤳ ν x) {a b : V.presheaf.stalk (ν x)}
    (hab : a - b ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk (ν x))) :
    ∃ c ∈ IsLocalRing.maximalIdeal (N.presheaf.stalk x), algebraMap _ N.functionField c =
      (ν.stalkMap (genericPoint N)).hom ((V.presheaf.stalkSpecializes hsp).hom a) -
        (ν.stalkMap (genericPoint N)).hom ((V.presheaf.stalkSpecializes hsp).hom b) := by
  refine ⟨(ν.stalkMap x).hom (a - b), (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
    (IsLocalRing.mem_maximalIdeal _).mp hab ((isUnit_map_iff _ _).mp hu), ?_⟩
  rw [← map_sub, ← map_sub]
  exact (ν.stalkSpecializes_stalkMap_apply (genericPoint N) x
    ((genericPoint_spec N).specializes trivial) (a - b)).symm

section Multiplicity

open exteriorPower

variable {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX]

/-- **Forms divisible by a function.** For `w ∈ Ω²_{𝒪_{X,Γ}}` and `a ∈ 𝒪_{X,Γ}`, the image of
`a w` in `Ω²_{k(X)}` has order at least `ord_Γ(a)`. -/
private theorem ord_le_ordForm_topFormsMap_smul {d : ℕ} (hdim : topologicalKrullDim X = d)
    (Γ : Mori.PrimeDivisor X) (a : Γ.localRing)
    (w : letI := stalkAlgebra sX Γ.genericPoint; ⋀[Γ.localRing]^d Ω[Γ.localRing⁄k])
    (τ : RationalPluriForms sX d ((1 : ℕ) : ℤ))
    (hτ : letI := stalkAlgebra sX Γ.genericPoint
      letI := functionFieldAlgebra sX
      haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
      τ = formPow (topFormsMap k Γ.localRing X.functionField d (a • w)) 1)
    (h0 : τ ≠ 0) : X.ord (algebraMap Γ.localRing X.functionField a) Γ.genericPoint ≤ Γ.ordForm τ := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
    (show topologicalKrullDim X = ((d : ℕ) : WithBot ℕ∞) by rw [hdim])
  obtain ⟨σ, hσ, hσ0⟩ := Γ.exists_topForms_generator hd
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hσ ▸ Submodule.mem_top (x := w))
  rw [Γ.ordForm_eq τ hσ hσ0, hτ, ← hc, smul_smul, map_smul,
    algebra_compatible_smul X.functionField (a * c), formPow_smul, pow_one, formCoeff_smul]
  have h1 : formCoeff Γ.localRing hσ hσ0
      (formPow (topFormsMap k Γ.localRing X.functionField d σ) 1 :
        RationalPluriForms sX d ((1 : ℕ) : ℤ)) = 1 := by
    have := repr_smul_formPow (topFormsBasis Γ.localRing hσ hσ0) 1 1
    rwa [one_smul, topFormsBasis_apply] at this
  rw [h1, mul_one]
  have hac0 : algebraMap Γ.localRing X.functionField (a * c) ≠ 0 := by
    intro h
    apply h0
    rw [hτ, ← hc, smul_smul, map_smul, algebra_compatible_smul X.functionField (a * c), h,
      zero_smul]
    exact (PiTensorProduct.tprod X.functionField).map_coord_zero (0 : Fin 1) rfl
  have hc0 : algebraMap Γ.localRing X.functionField c ≠ 0 :=
    fun h => hac0 (by rw [map_mul, h, mul_zero])
  have ha0 : algebraMap Γ.localRing X.functionField a ≠ 0 :=
    fun h => hac0 (by rw [map_mul, h, zero_mul])
  rw [map_mul, Scheme.ord_mul ha0 hc0]
  have : 0 ≤ X.ord (algebraMap Γ.localRing X.functionField c) Γ.genericPoint :=
    zero_le_ord_algebraMap_localRing Γ hc0
  linarith

/-- **The order of `da ∧ db` bounds the multiplicity of `a`.** For `a, b ∈ 𝒪_{X,Γ}` on a normal
surface over a perfect field, `ord_Γ(da ∧ db) ≥ ord_Γ(a) - 1`. -/
private theorem ord_sub_one_le_ordForm_formPow_ιMulti (hdim : topologicalKrullDim X = 2)
    (Γ : Mori.PrimeDivisor X) (a b : Γ.localRing) (τ : RationalPluriForms sX 2 ((1 : ℕ) : ℤ))
    (hτ : letI := functionFieldAlgebra sX
      τ = formPow (ιMulti X.functionField 2 (Fin.cons (KaehlerDifferential.D k
        X.functionField (algebraMap Γ.localRing X.functionField a)) fun _ : Fin 1 =>
          KaehlerDifferential.D k X.functionField (algebraMap Γ.localRing X.functionField b))) 1)
    (h0 : τ ≠ 0) :
    X.ord (algebraMap Γ.localRing X.functionField a) Γ.genericPoint - 1 ≤ Γ.ordForm τ := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  haveI := Γ.isDiscreteValuationRing_localRing
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply h0
    rw [hτ, map_zero, map_zero,
      (ιMulti X.functionField 2).map_coord_zero (0 : Fin 2) (by simp)]
    exact (PiTensorProduct.tprod X.functionField).map_coord_zero (0 : Fin 1) rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Γ.localRing
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  have hϖ0 : algebraMap Γ.localRing X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  have hϖ1 : X.ord (algebraMap Γ.localRing X.functionField ϖ) Γ.genericPoint = 1 :=
    (Scheme.ord_eq_iff Γ.coheight_genericPoint hϖ0).mpr (Ring.ordFrac_irreducible hϖ)
  have hv0 : algebraMap Γ.localRing X.functionField v ≠ 0 := (v.isUnit.map _).ne_zero
  have hord : ∀ j : ℕ, X.ord (algebraMap Γ.localRing X.functionField (↑v * ϖ ^ j))
      Γ.genericPoint = j := fun j => by
    rw [map_mul, map_pow, Scheme.ord_mul hv0 (pow_ne_zero _ hϖ0),
      Γ.ord_algebraMap_of_isUnit v.isUnit, zero_add,
      show (algebraMap Γ.localRing X.functionField ϖ) ^ j =
        (algebraMap Γ.localRing X.functionField ϖ) ^ (j : ℤ) from (zpow_natCast _ _).symm,
      MMP.Mori.ord_zpow _ hϖ0, hϖ1, mul_one]
  rw [hord]
  rcases n with _ | j
  · have := zero_le_ordForm_formPow_ιMulti hdim Γ _ b τ hτ h0
    push_cast; linarith
  -- `d(v ϖ^{j+1}) = ϖ^j ((j+1) v dϖ + ϖ dv)`
  have hD : KaehlerDifferential.D k Γ.localRing (↑v * ϖ ^ (j + 1)) =
      ϖ ^ j • ((((j + 1 : ℕ) : Γ.localRing) * ↑v) • KaehlerDifferential.D k Γ.localRing ϖ +
        ϖ • KaehlerDifferential.D k Γ.localRing ↑v) := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, Nat.add_sub_cancel]
    module
  set w := ιMulti Γ.localRing 2 (Fin.cons ((((j + 1 : ℕ) : Γ.localRing) * ↑v) •
      KaehlerDifferential.D k Γ.localRing ϖ + ϖ • KaehlerDifferential.D k Γ.localRing ↑v)
    fun _ : Fin 1 => KaehlerDifferential.D k Γ.localRing b) with hwdef
  have hw : topFormsMap k Γ.localRing X.functionField 2 (ιMulti Γ.localRing 2
      (Fin.cons (KaehlerDifferential.D k Γ.localRing (↑v * ϖ ^ (j + 1)))
        fun _ : Fin 1 => KaehlerDifferential.D k Γ.localRing b)) =
      ιMulti X.functionField 2 (Fin.cons (KaehlerDifferential.D k X.functionField
        (algebraMap Γ.localRing X.functionField (↑v * ϖ ^ (j + 1)))) fun _ : Fin 1 =>
          KaehlerDifferential.D k X.functionField (algebraMap Γ.localRing X.functionField b)) := by
    rw [topFormsMap_ιMulti]
    congr 1
    funext i
    refine Fin.cases ?_ (fun l => ?_) i <;>
      simp only [Fin.cons_zero, Fin.cons_succ, KaehlerDifferential.map_D]
  have hτw : τ = formPow (topFormsMap k Γ.localRing X.functionField 2 (ϖ ^ j • w)) 1 := by
    rw [hτ, ← hw, hD, hwdef, ← ιMulti_cons_smul]
  have := ord_le_ordForm_topFormsMap_smul hdim Γ (ϖ ^ j) w τ hτw h0
  rw [map_pow, show (algebraMap Γ.localRing X.functionField ϖ) ^ j =
      (algebraMap Γ.localRing X.functionField ϖ) ^ (j : ℤ) from (zpow_natCast _ _).symm,
    MMP.Mori.ord_zpow _ hϖ0, hϖ1, mul_one] at this
  push_cast
  linarith

/-- **The order of `da` bounds the multiplicity of `a`** on a normal curve: for `a ∈ 𝒪_{X,Γ}`,
`ord_Γ(da) ≥ ord_Γ(a) - 1`. -/
private theorem ord_sub_one_le_ordForm_d (hdim : topologicalKrullDim X = 1)
    (Γ : Mori.PrimeDivisor X) (a : Γ.localRing) (τ : RationalPluriForms sX 1 ((1 : ℕ) : ℤ))
    (hτ : letI := functionFieldAlgebra sX
      τ = formPow (ιMulti X.functionField 1 fun _ : Fin 1 => KaehlerDifferential.D k
        X.functionField (algebraMap Γ.localRing X.functionField a)) 1)
    (h0 : τ ≠ 0) :
    X.ord (algebraMap Γ.localRing X.functionField a) Γ.genericPoint - 1 ≤ Γ.ordForm τ := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  haveI := Γ.isDiscreteValuationRing_localRing
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply h0
    rw [hτ, map_zero, map_zero,
      (ιMulti X.functionField 1).map_coord_zero (0 : Fin 1) rfl]
    exact (PiTensorProduct.tprod X.functionField).map_coord_zero (0 : Fin 1) rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Γ.localRing
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  have hϖ0 : algebraMap Γ.localRing X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  have hϖ1 : X.ord (algebraMap Γ.localRing X.functionField ϖ) Γ.genericPoint = 1 :=
    (Scheme.ord_eq_iff Γ.coheight_genericPoint hϖ0).mpr (Ring.ordFrac_irreducible hϖ)
  have hv0 : algebraMap Γ.localRing X.functionField v ≠ 0 := (v.isUnit.map _).ne_zero
  have hord : ∀ j : ℕ, X.ord (algebraMap Γ.localRing X.functionField (↑v * ϖ ^ j))
      Γ.genericPoint = j := fun j => by
    rw [map_mul, map_pow, Scheme.ord_mul hv0 (pow_ne_zero _ hϖ0),
      Γ.ord_algebraMap_of_isUnit v.isUnit, zero_add,
      show (algebraMap Γ.localRing X.functionField ϖ) ^ j =
        (algebraMap Γ.localRing X.functionField ϖ) ^ (j : ℤ) from (zpow_natCast _ _).symm,
      MMP.Mori.ord_zpow _ hϖ0, hϖ1, mul_one]
  rw [hord]
  rcases n with _ | j
  · have hτ0 : 0 ≤ Γ.ordForm τ := by
      have := ord_le_ordForm_topFormsMap_smul (d := 1) hdim Γ 1
        (ιMulti Γ.localRing 1 fun _ : Fin 1 => KaehlerDifferential.D k Γ.localRing (↑v * ϖ ^ 0))
        τ (by
          rw [hτ, one_smul, topFormsMap_ιMulti]
          congr 2
          funext i
          simp [KaehlerDifferential.map_D]) h0
      rwa [map_one, (Scheme.ord_eq_iff (n := 0) Γ.coheight_genericPoint one_ne_zero).2
        (by simp)] at this
    push_cast; linarith
  have hD : KaehlerDifferential.D k Γ.localRing (↑v * ϖ ^ (j + 1)) =
      ϖ ^ j • ((((j + 1 : ℕ) : Γ.localRing) * ↑v) • KaehlerDifferential.D k Γ.localRing ϖ +
        ϖ • KaehlerDifferential.D k Γ.localRing ↑v) := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, Nat.add_sub_cancel]
    module
  have hw : topFormsMap k Γ.localRing X.functionField 1 (ιMulti Γ.localRing 1
      fun _ : Fin 1 => KaehlerDifferential.D k Γ.localRing (↑v * ϖ ^ (j + 1))) =
      ιMulti X.functionField 1 fun _ : Fin 1 => KaehlerDifferential.D k X.functionField
        (algebraMap Γ.localRing X.functionField (↑v * ϖ ^ (j + 1))) := by
    rw [topFormsMap_ιMulti]
    congr 1
    funext i
    simp only [KaehlerDifferential.map_D]
  have hτw : τ = formPow (topFormsMap k Γ.localRing X.functionField 1 (ϖ ^ j •
      ιMulti Γ.localRing 1 fun _ : Fin 1 => (((j + 1 : ℕ) : Γ.localRing) * ↑v) •
        KaehlerDifferential.D k Γ.localRing ϖ + ϖ • KaehlerDifferential.D k Γ.localRing ↑v)) 1 := by
    rw [hτ, ← hw, hD]
    congr 2
    have := (ιMulti Γ.localRing 1 (M := Ω[Γ.localRing⁄k])).map_smul_univ (fun _ => ϖ ^ j)
      (fun _ => (((j + 1 : ℕ) : Γ.localRing) * ↑v) • KaehlerDifferential.D k Γ.localRing ϖ +
        ϖ • KaehlerDifferential.D k Γ.localRing ↑v)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one] at this
    exact this
  have := ord_le_ordForm_topFormsMap_smul (d := 1) hdim Γ (ϖ ^ j) _ τ hτw h0
  rw [map_pow, show (algebraMap Γ.localRing X.functionField ϖ) ^ j =
      (algebraMap Γ.localRing X.functionField ϖ) ^ (j : ℤ) from (zpow_natCast _ _).symm,
    MMP.Mori.ord_zpow _ hϖ0, hϖ1, mul_one] at this
  push_cast
  linarith

end Multiplicity

end BisectionB7

section BisectionB8

variable {k : Type} [Field k] [PerfectField k] {V N : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
  [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [IsIntegral N]
  [LocallyOfFiniteType sV]

/-- **The residue along a branch through a presented point.** If `Ω = c (p⁻¹ dp ∧ du)^{⊗m}` at a
point `y` of the prime divisor `P = ν(N)`, with `p` of order one along `P`, then every residue of
`Ω` along `ν` is `c̄ (dū)^{⊗m}`. -/
private theorem residue_eq_of_presentation (ν : N ⟶ V) [LocallyOfFiniteType (ν ≫ sV)]
    (P : Mori.PrimeDivisor V)
    (hP : ν (genericPoint N) = P.genericPoint)
    (hsurj : Function.Surjective (ν.stalkMap (genericPoint N)).hom)
    {y : V} (hsp : ν (genericPoint N) ⤳ y) {p c uy : V.presheaf.stalk y}
    (hp1 : V.ord (algebraMap _ V.functionField p) P.genericPoint = 1) {m : ℕ}
    (Ω : RationalPluriForms sV 2 m)
    (hΩ : letI := stalkAlgebra sV y; letI := functionFieldAlgebra sV
      Ω = (algebraMap _ V.functionField c • formPow ((algebraMap _ V.functionField p)⁻¹ •
        exteriorPower.ιMulti V.functionField 2
          (Fin.cons (KaehlerDifferential.D k V.functionField (algebraMap _ _ p))
            fun _ : Fin 1 => KaehlerDifferential.D k V.functionField (algebraMap _ _ uy))) m :
        RationalPluriForms sV 2 m))
    {ρ : RationalPluriForms (ν ≫ sV) 1 m} (hρ : IsPoincareResidue sV ν 1 m Ω ρ) :
    letI := functionFieldAlgebra (ν ≫ sV)
    ρ = (ν.stalkMap (genericPoint N)).hom ((V.presheaf.stalkSpecializes hsp).hom c) •
      formPow (exteriorPower.ιMulti N.functionField 1 fun _ : Fin 1 =>
        KaehlerDifferential.D k N.functionField
          ((ν.stalkMap (genericPoint N)).hom ((V.presheaf.stalkSpecializes hsp).hom uy))) m := by
  letI := stalkAlgebra sV y
  letI := functionFieldAlgebra sV
  letI := functionFieldAlgebra (ν ≫ sV)
  haveI := isScalarTower_stalk_functionField sV y
  have hspalg : ∀ a : V.presheaf.stalk y, algebraMap _ V.functionField
      ((V.presheaf.stalkSpecializes hsp).hom a) = algebraMap _ V.functionField a :=
    MMP.Mori.algebraMap_stalkSpecializes hsp
  refine IsPoincareResidue.unique_of_surjective P hP hsurj hρ
    ⟨(V.presheaf.stalkSpecializes hsp).hom p, (V.presheaf.stalkSpecializes hsp).hom c,
      fun _ => (V.presheaf.stalkSpecializes hsp).hom uy, by rw [hspalg, hP, hp1], ?_, rfl⟩
  simp only [hspalg]
  exact hΩ

end BisectionB8

section BisectionB9

/-- **Differentials survive a formally smooth extension.** If `S → T` is a formally smooth
extension of fields over `R` and `ds ≠ 0` in `Ω_{S/R}`, then `ds ≠ 0` in `Ω_{T/R}`: the map
`T ⊗_S Ω_{S/R} → Ω_{T/R}` is injective, its kernel being the image of `H₁(L_{T/S}) = 0`. -/
private theorem D_algebraMap_ne_zero_of_formallySmooth (R S T : Type*) [CommRing R] [Field S] [Field T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Algebra.FormallySmooth S T]
    {s : S} (hs : KaehlerDifferential.D R S s ≠ 0) :
    KaehlerDifferential.D R T (algebraMap S T s) ≠ 0 := by
  intro h0
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R S T) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  have h1 : KaehlerDifferential.mapBaseChange R S T
      ((1 : T) ⊗ₜ[S] KaehlerDifferential.D R S s) = 0 := by
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D, h0]
  have h2 := hinj (h1.trans (map_zero _).symm)
  exact hs ((Module.FaithfullyFlat.one_tmul_eq_zero_iff S Ω[S⁄R] (A := T)
    (KaehlerDifferential.D R S s)).mp h2)

end BisectionB9

section BisectionB10

variable {k : Type} [Field k] [CharZero k]

/-- **Pulled back differentials do not vanish.** Along a dominant morphism of integral schemes of
finite type over a field of characteristic zero, the differential of the pull-back of a function
with nonzero differential is nonzero: the extension of function fields is separably generated,
hence formally smooth. -/
private theorem D_functionFieldMap_ne_zero {X Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (hf : f ≫ sY = sX) [LocallyOfFiniteType sX]
    {s : Y.functionField} (hs : letI := functionFieldAlgebra sY
      KaehlerDifferential.D k Y.functionField s ≠ 0) :
    letI := functionFieldAlgebra sX
    KaehlerDifferential.D k X.functionField (functionFieldMap f s) ≠ 0 := by
  subst hf
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (f ≫ sY)
  letI := functionFieldMapAlgebra f
  haveI := isScalarTower_functionFieldMap sY f
  have : CharZero Y.functionField :=
    charZero_of_injective_algebraMap (algebraMap k Y.functionField).injective
  have := essFiniteType_functionField (sX := f ≫ sY)
  have : Algebra.EssFiniteType Y.functionField X.functionField :=
    Algebra.EssFiniteType.of_comp k Y.functionField X.functionField
  exact D_algebraMap_ne_zero_of_formallySmooth k Y.functionField X.functionField hs

/-- **A partner differential.** On an integral scheme of finite type over `k` with function field
of transcendence degree two, every nonzero differential `dx` has a partner `dh` with
`dx ∧ dh ≠ 0`. -/
private theorem exists_ιMulti_D_ne_zero {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [LocallyOfFiniteType sX] (hd : topologicalKrullDim X = 2) {x : X.functionField}
    (hx : letI := functionFieldAlgebra sX; KaehlerDifferential.D k X.functionField x ≠ 0) :
    letI := functionFieldAlgebra sX
    ∃ h : X.functionField, exteriorPower.ιMulti X.functionField 2
      (Fin.cons (KaehlerDifferential.D k X.functionField x)
        fun _ : Fin 1 => KaehlerDifferential.D k X.functionField h) ≠ 0 := by
  letI := functionFieldAlgebra sX
  have := essFiniteType_functionField (sX := sX)
  have hd2 : (Algebra.trdeg k X.functionField).toNat = 2 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hd]; rfl)
  have hrank : Module.finrank X.functionField Ω[X.functionField⁄k] = 2 :=
    (finrank_kaehlerDifferential_eq_trdeg k X.functionField).trans hd2
  -- some `dh` is not a multiple of `dx`
  obtain ⟨h, hh⟩ : ∃ h : X.functionField, KaehlerDifferential.D k X.functionField h ∉
      Submodule.span X.functionField {KaehlerDifferential.D k X.functionField x} := by
    by_contra hcon
    push Not at hcon
    have hle : Submodule.span X.functionField (Set.range (KaehlerDifferential.D k
        X.functionField)) ≤ Submodule.span X.functionField
          {KaehlerDifferential.D k X.functionField x} := by
      rw [Submodule.span_le]; rintro - ⟨h, rfl⟩; exact hcon h
    rw [KaehlerDifferential.span_range_derivation, top_le_iff] at hle
    have := finrank_span_singleton (K := X.functionField) hx
    rw [hle, finrank_top, hrank] at this
    exact absurd this (by norm_num)
  refine ⟨h, fun h0 => ?_⟩
  -- `dx, dh` span `Ω`, so `dx ∧ dh` spans `Ω²`
  have hli : LinearIndependent X.functionField ![KaehlerDifferential.D k X.functionField x,
      KaehlerDifferential.D k X.functionField h] := by
    rw [LinearIndependent.pair_iff' hx]
    intro a ha
    exact hh (ha ▸ Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _))
  have hspan : Submodule.span X.functionField (Set.range ![KaehlerDifferential.D k
      X.functionField x, KaehlerDifferential.D k X.functionField h]) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, Fintype.card_fin, hrank]
  have htop := exteriorPower.ιMulti_span_of_span (R := X.functionField) (n := 2)
    (M := Ω[X.functionField⁄k]) hspan
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) (d := 2) (by rw [hd]; norm_cast)
  apply b.ne_zero ()
  have hmem : b () ∈ Submodule.span X.functionField (exteriorPower.ιMulti X.functionField 2 ''
      {a | Set.range a ⊆ Set.range ![KaehlerDifferential.D k X.functionField x,
        KaehlerDifferential.D k X.functionField h]}) := htop ▸ Submodule.mem_top
  have hzero : ∀ a : Fin 2 → Ω[X.functionField⁄k], Set.range a ⊆
      Set.range ![KaehlerDifferential.D k X.functionField x,
        KaehlerDifferential.D k X.functionField h] →
      exteriorPower.ιMulti X.functionField 2 a = 0 := by
    intro a ha
    have h0' : ∀ i, a i = KaehlerDifferential.D k X.functionField x ∨
        a i = KaehlerDifferential.D k X.functionField h := fun i => by
      obtain ⟨j, hj⟩ := ha ⟨i, rfl⟩
      fin_cases j
      · exact Or.inl hj.symm
      · exact Or.inr hj.symm
    have hav : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
    have hc : (Fin.cons (KaehlerDifferential.D k X.functionField x)
        fun _ : Fin 1 => KaehlerDifferential.D k X.functionField h : Fin 2 → _) =
        ![KaehlerDifferential.D k X.functionField x, KaehlerDifferential.D k X.functionField h] :=
      by ext i; fin_cases i <;> rfl
    rw [hc] at h0
    rcases h0' 0 with h1 | h1 <;> rcases h0' 1 with h2 | h2 <;> rw [hav, h1, h2]
    · exact (exteriorPower.ιMulti X.functionField 2).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl
        (by decide)
    · exact h0
    · have hsw : ![KaehlerDifferential.D k X.functionField h, KaehlerDifferential.D k
          X.functionField x] = ![KaehlerDifferential.D k X.functionField x,
            KaehlerDifferential.D k X.functionField h] ∘ Equiv.swap (0 : Fin 2) 1 := by
        ext i; fin_cases i <;> rfl
      have hs := (exteriorPower.ιMulti X.functionField 2).map_swap_add
        ![KaehlerDifferential.D k X.functionField x, KaehlerDifferential.D k X.functionField h]
        (by decide : (0 : Fin 2) ≠ 1)
      rw [h0, add_zero] at hs
      rw [hsw]
      exact hs
    · exact (exteriorPower.ιMulti X.functionField 2).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl
        (by decide)
  have hsub : exteriorPower.ιMulti X.functionField 2 '' {a | Set.range a ⊆
      Set.range ![KaehlerDifferential.D k X.functionField x,
        KaehlerDifferential.D k X.functionField h]} ⊆ {0} := by
    rintro - ⟨a, ha, rfl⟩; exact hzero a ha
  have := Submodule.span_mono hsub hmem
  rwa [Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot] at this

/-- **General prime divisors carry no multiple fibre of `x`.** On a normal surface over a perfect
field, for `dx ≠ 0` there are finitely many prime divisors `E` outside of which every regular `a`
with `da = dx` vanishes to order at most one along `E`: away from the divisor of `dx ∧ dh` and the
poles of `h`, `ord_E(a) - 1 ≤ ord_E(da ∧ dh) = 0`. -/
private theorem exists_finite_ord_le_one [PerfectField k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hd : topologicalKrullDim X = 2) {x : X.functionField}
    (hx : letI := functionFieldAlgebra sX; KaehlerDifferential.D k X.functionField x ≠ 0) :
    letI := functionFieldAlgebra sX
    ∃ Z : Set (Mori.PrimeDivisor X), Z.Finite ∧ ∀ E : Mori.PrimeDivisor X, E ∉ Z →
      ∀ a : E.localRing, KaehlerDifferential.D k X.functionField
        (algebraMap E.localRing X.functionField a) = KaehlerDifferential.D k X.functionField x →
      algebraMap E.localRing X.functionField a ≠ 0 →
      X.ord (algebraMap E.localRing X.functionField a) E.genericPoint ≤ 1 := by
  classical
  letI := functionFieldAlgebra sX
  obtain ⟨h, hh⟩ := exists_ιMulti_D_ne_zero sX hd hx
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ : RationalPluriForms sX 2 ((1 : ℕ) : ℤ), τ = formPow
      (exteriorPower.ιMulti X.functionField 2 (Fin.cons (KaehlerDifferential.D k X.functionField x)
        fun _ : Fin 1 => KaehlerDifferential.D k X.functionField h)) 1 := ⟨_, rfl⟩
  have hτ₀0 : τ₀ ≠ 0 := hτ₀ ▸ formPow_ne_zero_of_ne_zero (sX := sX) hd hh 1
  have hh0 : h ≠ 0 := by
    rintro rfl
    apply hh
    rw [map_zero]
    exact (exteriorPower.ιMulti X.functionField 2).map_coord_zero (1 : Fin 2) rfl
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero hh0
  refine ⟨{E | E.ordForm τ₀ ≠ 0} ∪ {E | X.ord h E.genericPoint ≠ 0},
    (finite_ordForm_ne_zero τ₀).union ((finite_ord_ne_zero φ).subset fun E hE => by
      change Mori.PrimeDivisor.ord E φ ≠ 0; rw [hφ]; exact hE), fun E hE a ha ha0 => ?_⟩
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hE
  obtain ⟨b, hb⟩ : h ∈ (algebraMap E.localRing X.functionField).range := by
    rw [← E.divisorialValuation_le_one_iff, ← zero_le_ord_iff E hh0, hE.2]
  have hτ : τ₀ = formPow (exteriorPower.ιMulti X.functionField 2 (Fin.cons
      (KaehlerDifferential.D k X.functionField (algebraMap E.localRing X.functionField a))
        fun _ : Fin 1 => KaehlerDifferential.D k X.functionField
          (algebraMap E.localRing X.functionField b))) 1 := by
    rw [hτ₀, ha, hb]
  have := ord_sub_one_le_ordForm_formPow_ιMulti hd E a b τ₀ hτ hτ₀0
  rw [hE.1] at this
  omega

end BisectionB10

section BisectionB12

open scoped WithZero

open MMP.Fourfold.SNCWeight.SNCModel (Dominates)

variable {k : Type} [Field k] {N T : Scheme.{0}} [IsIntegral N] [IsLocallyNoetherian N]
  [IsNormal N] [IsIntegral T] {sN : N ⟶ Spec (.of k)}

/-- **The transported valuation of a prime divisor.** For an automorphism `σ` of `k(N)` over
`k(T)`, `N` a normal curve proper over `T`, and a prime divisor `Q` of `N` over a closed point of
`T`, the valuation `v_Q ∘ σ` is the valuation of a prime divisor `Q'` over the same point. -/
private theorem exists_primeDivisor_ord_comp_eq (hdimN : topologicalKrullDim N = 1) (φ : N ⟶ T)
    [IsProper φ] [IsDominant φ] (σ : FunctionFieldEquiv sN sN)
    (hσ : ∀ a, σ (functionFieldMap φ a) = functionFieldMap φ a) (Q : Mori.PrimeDivisor N)
    (hQ : φ Q.genericPoint ≠ genericPoint T) :
    ∃ Q' : Mori.PrimeDivisor N, φ Q'.genericPoint = φ Q.genericPoint ∧
      ∀ a : N.functionField, a ≠ 0 → N.ord (σ a) Q.genericPoint = N.ord a Q'.genericPoint := by
  letI := functionFieldAlgebra sN
  obtain ⟨x', hdom, hx'⟩ := exists_dominates_comap φ σ hσ Q
  have hx'η : x' ≠ genericPoint N := by
    rintro rfl; rw [map_genericPoint_of_isDominant] at hx'; exact hQ hx'.symm
  obtain ⟨Q', rfl⟩ : ∃ Q' : Mori.PrimeDivisor N, Q'.genericPoint = x' :=
    ⟨_, AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x'
      (coheight_eq_one_of_ne_genericPoint hdimN hx'η)⟩
  refine ⟨Q', hx', ?_⟩
  haveI := Q'.isDiscreteValuationRing_localRing
  have hσ0 : ∀ a : N.functionField, a ≠ 0 → σ a ≠ 0 := fun a ha h =>
    ha (σ.injective (h.trans (map_zero σ).symm))
  -- domination on units and on the maximal ideal
  have hunit : ∀ u : Q'.localRing, IsUnit u →
      N.ord (σ (algebraMap _ N.functionField u)) Q.genericPoint = 0 := by
    intro u hu
    have hu0 : algebraMap Q'.localRing N.functionField u ≠ 0 := (hu.map _).ne_zero
    have h1 := hdom.1 u
    have h2 := hdom.1 ↑(hu.unit⁻¹)
    rw [Valuation.comap_apply] at h1 h2
    change Q.divisorialValuation (σ _) ≤ 1 at h1
    change Q.divisorialValuation (σ _) ≤ 1 at h2
    rw [← zero_le_ord_iff Q (hσ0 _ hu0)] at h1
    have hinv : algebraMap Q'.localRing N.functionField ↑(hu.unit⁻¹) =
        (algebraMap Q'.localRing N.functionField u)⁻¹ := by
      rw [map_units_inv, IsUnit.unit_spec]
    rw [hinv, map_inv₀] at h2
    rw [← zero_le_ord_iff Q (inv_ne_zero (hσ0 _ hu0)),
      show (σ (algebraMap Q'.localRing N.functionField u))⁻¹ =
        (σ (algebraMap Q'.localRing N.functionField u)) ^ (-1 : ℤ) from (zpow_neg_one _).symm,
      MMP.Mori.ord_zpow _ (hσ0 _ hu0)] at h2
    omega
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Q'.localRing
  have hϖ0 : algebraMap Q'.localRing N.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  have hϖ1 : N.ord (algebraMap Q'.localRing N.functionField ϖ) Q'.genericPoint = 1 :=
    (Scheme.ord_eq_iff Q'.coheight_genericPoint hϖ0).mpr (Ring.ordFrac_irreducible hϖ)
  set e := N.ord (σ (algebraMap Q'.localRing N.functionField ϖ)) Q.genericPoint with hedef
  have he1 : 1 ≤ e := by
    have h := hdom.2 ϖ hϖ.not_isUnit
    rw [Valuation.comap_apply] at h
    change Q.divisorialValuation (σ _) < 1 at h
    exact (one_le_ord_iff Q (hσ0 _ hϖ0)).mpr h
  have hmul : ∀ a : N.functionField, a ≠ 0 →
      N.ord (σ a) Q.genericPoint = e * N.ord a Q'.genericPoint := by
    intro a ha
    obtain ⟨u, hu, hua⟩ := exists_isUnit_eq_mul_zpow Q'.coheight_genericPoint hϖ1 ha
    have hu0 : algebraMap Q'.localRing N.functionField u ≠ 0 := (hu.map _).ne_zero
    rw [hua, map_mul, map_zpow₀, Scheme.ord_mul (hσ0 _ hu0) (zpow_ne_zero _ (hσ0 _ hϖ0)),
      hunit u hu, MMP.Mori.ord_zpow _ (hσ0 _ hϖ0), ← hua]
    ring
  -- `e = 1`, testing on the inverse image of a uniformizer at `Q`
  haveI := Q.isDiscreteValuationRing_localRing
  obtain ⟨ϖQ, hϖQ⟩ := IsDiscreteValuationRing.exists_irreducible Q.localRing
  have hϖQ0 : algebraMap Q.localRing N.functionField ϖQ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖQ.ne_zero
  have hϖQ1 : N.ord (algebraMap Q.localRing N.functionField ϖQ) Q.genericPoint = 1 :=
    (Scheme.ord_eq_iff Q.coheight_genericPoint hϖQ0).mpr (Ring.ordFrac_irreducible hϖQ)
  have hb0 : σ.symm (algebraMap Q.localRing N.functionField ϖQ) ≠ 0 := fun h =>
    hϖQ0 (σ.symm.injective (h.trans (map_zero σ.symm).symm))
  have h1 := hmul _ hb0
  rw [AlgEquiv.apply_symm_apply, hϖQ1] at h1
  have he : e = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1.symm with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · omega
  intro a ha
  rw [hmul a ha, he, one_mul]

/-- **Orders of forms under a field automorphism.** If `ord_Q ∘ σ = ord_{Q'}` on a curve, the
pull-back of a pluricanonical form along `σ` has the same order at `Q` as the form at `Q'`. -/
private theorem ordForm_pluriformPullback_eq [CharZero k] [IsAlgClosed k] [LocallyOfFiniteType sN]
    (hdimN : topologicalKrullDim N = 1) (hN : IsNormalVariety k sN) (σ : FunctionFieldEquiv sN sN)
    (Q Q' : Mori.PrimeDivisor N)
    (hQ : ∀ a : N.functionField, a ≠ 0 → N.ord (σ a) Q.genericPoint = N.ord a Q'.genericPoint)
    {m : ℕ} (ρ : RationalPluriForms sN 1 m) (hρ : ρ ≠ 0) :
    Q.ordForm (pluriformPullback sN sN (FunctionFieldEquiv.toHom sN sN σ) 1 m ρ) = Q'.ordForm ρ := by
  letI := functionFieldAlgebra sN
  obtain ⟨p, -, hp1⟩ := exists_ord_eq_one Q'.coheight_genericPoint
  set z := algebraMap _ N.functionField p with hzdef
  have hd1 : topologicalKrullDim N = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdimN
  obtain ⟨hω0, hωR⟩ := MMP.Flips.ordForm_d_eq_zero hN hdimN Q' z hp1 _ rfl
  have hι0' : exteriorPower.ιMulti N.functionField 1
      (fun _ : Fin 1 => KaehlerDifferential.D k N.functionField z) ≠ 0 := fun h =>
    hω0 (by rw [h]; exact (PiTensorProduct.tprod _).map_coord_zero (0 : Fin 1) rfl)
  have hz0 : KaehlerDifferential.D k N.functionField z ≠ 0 := fun h0 =>
    hι0' (by rw [h0]; exact (exteriorPower.ιMulti N.functionField 1).map_coord_zero (0 : Fin 1) rfl)
  have hι0 := ιMulti_fin_one_ne_zero (R := N.functionField) hz0
  obtain ⟨b⟩ := exists_basis_topForms (sX := sN) (d := 1) (by rw [hdimN]; norm_cast)
  obtain ⟨ωz, hωz⟩ : ∃ ω : RationalPluriForms sN 1 m, ω = formPow
      (exteriorPower.ιMulti N.functionField 1 fun _ : Fin 1 =>
        KaehlerDifferential.D k N.functionField z) m := ⟨_, rfl⟩
  have hωz0 : ωz ≠ 0 := hωz ▸ formPow_ne_zero_of_ne_zero (sX := sN) hdimN hι0 m
  have hrepr0 : (ZTensorPower.basis b m).repr ωz () ≠ 0 :=
    MMP.Mori.repr_ne_zero_of_ne_zero b hωz0
  set θ := (ZTensorPower.basis b m).repr ρ () / (ZTensorPower.basis b m).repr ωz ()
  have hρθ : ρ = θ • ωz := eq_div_repr_smul b ρ ωz hrepr0
  have hθ0 : θ ≠ 0 := by rintro h; apply hρ; rw [hρθ, h, zero_smul]
  rw [hρθ, hωz]
  erw [pluriformPullback_smul_formPow_D sN sN hdimN hdimN _ z θ hz0 m]
  change Q.ordForm (show RationalPluriForms sN 1 m from σ θ • formPow
    (exteriorPower.ιMulti N.functionField 1 fun _ : Fin 1 =>
      KaehlerDifferential.D k N.functionField (σ z)) m) = _
  have hσz : N.ord (σ z) Q.genericPoint = 1 := by
    rw [hQ z (fun h => by rw [h] at hp1; simp at hp1), hp1]
  obtain ⟨hω0', hωR'⟩ := MMP.Flips.ordForm_d_eq_zero hN hdimN Q (σ z) hσz _ rfl
  have hι0'' : exteriorPower.ιMulti N.functionField 1
      (fun _ : Fin 1 => KaehlerDifferential.D k N.functionField (σ z)) ≠ 0 := fun h =>
    hω0' (by rw [h]; exact (PiTensorProduct.tprod _).map_coord_zero (0 : Fin 1) rfl)
  have hz0' : KaehlerDifferential.D k N.functionField (σ z) ≠ 0 := fun h0 =>
    hι0'' (by rw [h0]; exact (exteriorPower.ιMulti N.functionField 1).map_coord_zero (0 : Fin 1) rfl)
  have hσθ0 : σ θ ≠ 0 := fun h => hθ0 (σ.injective (h.trans (map_zero σ).symm))
  rw [ordForm_smul_formPow (sX := sN) hd1 Q (ιMulti_fin_one_ne_zero hz0') hσθ0 m _ rfl _ rfl]
  erw [ordForm_smul_formPow (sX := sN) hd1 Q' hι0 hθ0 m _ rfl _ rfl]
  erw [hωR', hωR]
  rw [hQ θ hθ0]

/-- **Crepancy of an automorphism of a curve pair.** If the transported valuation `v_Q ∘ σ` of
every prime divisor `Q` is that of a prime divisor `Q'` with the same boundary coefficient, then
`σ` is crepant for `(N, Θ)`. -/
private theorem isCrepantBirationalMap_of_ord_comp_eq [PerfectField k] (hN : IsNormalVariety k sN)
    (hdimN : topologicalKrullDim N = 1) {Θ : QDivisor N} (hP : MMP.Mori.IsPair sN Θ)
    (σ : FunctionFieldEquiv sN sN)
    (hΘ : ∀ Q : Mori.PrimeDivisor N, ∃ Q' : Mori.PrimeDivisor N, (∀ a : N.functionField, a ≠ 0 →
      N.ord (σ a) Q.genericPoint = N.ord a Q'.genericPoint) ∧ Θ.coeff Q' = Θ.coeff Q)
    (hΘ' : letI := functionFieldAlgebra sN; ∀ Q : Mori.PrimeDivisor N, ∃ Q' : Mori.PrimeDivisor N, (∀ a : N.functionField, a ≠ 0 →
      N.ord (σ.symm a) Q.genericPoint = N.ord a Q'.genericPoint) ∧ Θ.coeff Q' = Θ.coeff Q) :
    IsCrepantBirationalMap sN sN Θ Θ σ := by
  letI := functionFieldAlgebra sN
  -- one direction, for an automorphism and its data
  have key : ∀ (τ : FunctionFieldEquiv sN sN), (∀ Q : Mori.PrimeDivisor N,
      ∃ Q' : Mori.PrimeDivisor N, (∀ a : N.functionField, a ≠ 0 →
        N.ord (τ a) Q.genericPoint = N.ord a Q'.genericPoint) ∧ Θ.coeff Q' = Θ.coeff Q) →
      ∀ (v : Valuation N.functionField ℤᵐ⁰) (a : ℝ), HasLogDiscrepancy sN Θ v a →
        HasLogDiscrepancy sN Θ (v.comap τ.toRingEquiv.toRingHom) a := by
    intro τ hτ v a h
    obtain ⟨n, D, hDv, hD⟩ := h
    obtain ⟨P, hPv⟩ := exists_primeDivisor_valuation_eq_of_dim_eq_one hN hdimN D
    obtain ⟨Q', hQ'ord, hQ'Θ⟩ := hτ P
    let D' : DivisorOver k sN := DivisorOver.ofPrimeDivisor k hN Q'
    have hD'v : D'.valuation = v.comap τ.toRingEquiv.toRingHom := by
      ext b
      rw [← hDv, hPv]
      change Q'.valuationOver (𝟙 N) b = P.valuationOver (𝟙 N) (τ b)
      rw [PrimeDivisor.valuationOver_apply, PrimeDivisor.valuationOver_apply,
        functionFieldMap_id_apply, functionFieldMap_id_apply]
      by_cases hb : b = 0
      · rw [hb, map_zero, map_zero, map_zero]
      have hτb : τ b ≠ 0 := fun h => hb (τ.injective (h.trans (map_zero τ).symm))
      rw [Q'.divisorialValuation_eq_exp_neg_ord hb, P.divisorialValuation_eq_exp_neg_ord hτb,
        hQ'ord b hb]
    obtain ⟨-, n', K', hK', -⟩ := id hP
    obtain ⟨cQ, hcQ⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK' D'
    have hlogQ := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hcQ
      (inferInstance : IsProper (𝟙 N))
    obtain ⟨cP, hcP⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK'
      (DivisorOver.ofPrimeDivisor k hN P)
    have hlogP := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hcP
      (inferInstance : IsProper (𝟙 N))
    have e2 := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hD hlogP hPv
    have e3 := hcQ.eq_neg_coeff_of_ofPrimeDivisor hN
    have e4 := hcP.eq_neg_coeff_of_ofPrimeDivisor hN
    refine ⟨n', D', hD'v, ?_⟩
    convert hlogQ using 1
    rw [e2, e3, e4, hQ'Θ]
  intro v a
  refine ⟨key σ hΘ v a, fun h => ?_⟩
  have h' := key σ.symm hΘ' _ a h
  have hv : (v.comap σ.toRingEquiv.toRingHom).comap σ.symm.toRingEquiv.toRingHom = v := by
    ext x
    change v (σ (σ.symm x)) = v x
    rw [AlgEquiv.apply_symm_apply]
  rwa [hv] at h'

end BisectionB12

section BisectionB13

open exteriorPower

open KaehlerDifferential TensorProduct IsLocalRing

variable (k : Type*) [Field k] {R : Type*} [CommRing R] [IsLocalRing R] [Algebra k R]

/-- **Differentials of a local ring along a uniformizer.** If the maximal ideal of `R` is generated
by `ϖ` and `dx̄` spans `Ω_{κ/k}`, then `dϖ, dx` span `Ω_{R/k}` (conormal sequence and
Nakayama). -/
private theorem span_D_pair_eq_top_of_uniformizer [Module.Finite R Ω[R⁄k]] {ϖ x : R}
    (hm : maximalIdeal R = Ideal.span {ϖ})
    (hx : Submodule.span (ResidueField R) {D k (ResidueField R) (residue R x)} = ⊤) :
    Submodule.span R {D k R ϖ, D k R x} = ⊤ := by
  rw [← IsLocalRing.map_tensorProduct_mk_eq_top, Submodule.map_span, eq_top_iff]
  intro v _
  have hex := exact_kerCotangentToTensor_mapBaseChange k R (ResidueField R) residue_surjective
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (hx ▸ Submodule.mem_top (x := mapBaseChange k R (ResidueField R) v))
  have hDx : mapBaseChange k R (ResidueField R) ((1 : ResidueField R) ⊗ₜ[R] D k R x) =
      D k (ResidueField R) (residue R x) := by
    rw [mapBaseChange_tmul, one_smul, map_D]; rfl
  have hker : mapBaseChange k R (ResidueField R)
      (v - c • ((1 : ResidueField R) ⊗ₜ[R] D k R x)) = 0 := by
    rw [map_sub, map_smul, hDx, hc, sub_self]
  obtain ⟨y, hy⟩ := (hex _).mp hker
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ y
  have ha : (a : R) ∈ Ideal.span {ϖ} := by rw [← hm, ← ker_residue]; exact a.2
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp ha
  have hϖ0 : algebraMap R (ResidueField R) ϖ = 0 :=
    (residue_eq_zero_iff _).mpr (hm ▸ Ideal.mem_span_singleton_self ϖ)
  have hy' : kerCotangentToTensor k R (ResidueField R)
      ((RingHom.ker (algebraMap R (ResidueField R))).toCotangent a) =
      algebraMap R (ResidueField R) r • ((1 : ResidueField R) ⊗ₜ[R] D k R ϖ) := by
    rw [kerCotangentToTensor_toCotangent, ← hr, Derivation.leibniz, tmul_add, tmul_smul,
      tmul_smul, ← algebraMap_smul (ResidueField R) r, ← algebraMap_smul (ResidueField R) ϖ,
      hϖ0, zero_smul, add_zero]
  have hv : v = c • ((1 : ResidueField R) ⊗ₜ[R] D k R x) +
      algebraMap R (ResidueField R) r • ((1 : ResidueField R) ⊗ₜ[R] D k R ϖ) := by
    rw [← hy', hy]; abel
  rw [hv]
  obtain ⟨c', rfl⟩ := IsLocalRing.residue_surjective c
  rw [← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul, algebraMap_smul]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, Or.inr rfl, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, Or.inl rfl, rfl⟩))

/-- If `da, db` span `Ω_{R/k}`, then `da ∧ db` spans `Ω²_{R/k}`. -/
private theorem span_ιMulti_eq_top_of_span_pair {a b : Ω[R⁄k]}
    (hspan : Submodule.span R {a, b} = ⊤) :
    Submodule.span R {exteriorPower.ιMulti R 2 ![a, b]} = ⊤ := by
  have h := exteriorPower.ιMulti_span_of_span (R := R) (n := 2) (M := Ω[R⁄k]) hspan
  rw [eq_top_iff, ← h, Submodule.span_le]
  rintro - ⟨v, hv, rfl⟩
  have h0 : v 0 = a ∨ v 0 = b := hv ⟨0, rfl⟩
  have h1 : v 1 = a ∨ v 1 = b := hv ⟨1, rfl⟩
  have hvv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rw [hvv, h0, h1]
  · rw [(exteriorPower.ιMulti R 2).map_eq_zero_of_eq ![a, a] (i := 0) (j := 1) rfl (by decide)]
    exact zero_mem _
  · exact Submodule.mem_span_singleton_self _
  · have : exteriorPower.ιMulti R 2 ![b, a] = -exteriorPower.ιMulti R 2 ![a, b] := by
      have hsw : ![b, a] = ![a, b] ∘ Equiv.swap (0 : Fin 2) 1 := by
        ext i; fin_cases i <;> rfl
      rw [hsw]
      exact eq_neg_of_add_eq_zero_left
        ((exteriorPower.ιMulti R 2).map_swap_add _ (by decide : (0 : Fin 2) ≠ 1))
    rw [this]
    exact neg_mem (Submodule.mem_span_singleton_self _)
  · rw [(exteriorPower.ιMulti R 2).map_eq_zero_of_eq ![b, b] (i := 0) (j := 1) rfl (by decide)]
    exact zero_mem _

/-- **Spanning differentials transfer along an isomorphism.** If `e : κ ≃ₐ[k] L` and every
differential of `L` is a multiple of `d(e x)`, then `dx` spans `Ω_{κ/k}`. -/
private theorem span_D_eq_top_of_algEquiv {κ L : Type*} [Field κ] [Field L] [Algebra k κ] [Algebra k L]
    (e : κ ≃ₐ[k] L) {x : κ} (hL : ∀ l : L, ∃ c : L, D k L l = c • D k L (e x)) :
    Submodule.span κ {D k κ x} = ⊤ := by
  letI : Algebra L κ := e.symm.toRingHom.toAlgebra
  haveI : IsScalarTower k L κ :=
    IsScalarTower.of_algebraMap_eq fun c => (e.symm.commutes c).symm
  rw [eq_top_iff, ← span_range_derivation k κ, Submodule.span_le]
  rintro - ⟨r, rfl⟩
  obtain ⟨c, hc⟩ := hL (e r)
  have h1 : KaehlerDifferential.map k k L κ (D k L (e r)) = D k κ r := by
    rw [map_D]; change D k κ (e.symm (e r)) = _; rw [AlgEquiv.symm_apply_apply]
  have h2 : KaehlerDifferential.map k k L κ (D k L (e x)) = D k κ x := by
    rw [map_D]; change D k κ (e.symm (e x)) = _; rw [AlgEquiv.symm_apply_apply]
  rw [← h1, hc, map_smul, h2, ← algebraMap_smul κ c]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

variable {k₀ : Type} [Field k₀] [PerfectField k₀] {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of k₀)}
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] {j : T ⟶ Y}
  [LocallyOfFiniteType sY]

/-- **A logarithmic frame along a prime divisor has a simple pole.** If `ϖ` is a uniformizer of
`𝒪_{Y,P}` and `dx̄` spans the differentials of the residue field, then
`ord_P(ϖ⁻¹ dϖ ∧ dx) = -1`. -/
private theorem ordForm_dlog_frame_eq_neg_one (P : Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint) (hdim : topologicalKrullDim Y = 2)
    {ϖ x : Y.presheaf.stalk (j (genericPoint T))}
    (hϖ : Y.ord (algebraMap _ Y.functionField ϖ) (j (genericPoint T)) = 1)
    (hx : letI := stalkAlgebra sY (j (genericPoint T))
      Submodule.span (ResidueField (Y.presheaf.stalk (j (genericPoint T))))
        {D k₀ (ResidueField (Y.presheaf.stalk (j (genericPoint T))))
          (residue _ x)} = ⊤)
    (τ : RationalPluriForms sY 2 ((1 : ℕ) : ℤ))
    (hτ : letI := functionFieldAlgebra sY
      τ = formPow ((algebraMap _ Y.functionField ϖ)⁻¹ • exteriorPower.ιMulti Y.functionField 2
        (Fin.cons (D k₀ Y.functionField (algebraMap _ _ ϖ))
          fun _ : Fin 1 => D k₀ Y.functionField (algebraMap _ _ x))) 1) :
    P.ordForm τ = -1 := by
  letI := stalkAlgebra sY (j (genericPoint T))
  letI := functionFieldAlgebra sY
  haveI := isScalarTower_stalk_functionField sY (j (genericPoint T))
  obtain ⟨hdvr, hfree, hfin, -, hcoh, -⟩ := stalk_facts_of_eq_genericPoint (sY := sY) P hP
  have hϖ0 : algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField ϖ ≠ 0 := by
    intro h; rw [h] at hϖ; simp at hϖ
  -- `ϖ` generates the maximal ideal
  have hm : maximalIdeal (Y.presheaf.stalk (j (genericPoint T))) = Ideal.span {ϖ} := by
    obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible
      (Y.presheaf.stalk (j (genericPoint T)))
    have hϖ'0 : algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField ϖ' ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ'.ne_zero
    have h1 := (Scheme.ord_eq_iff hcoh hϖ0).mp hϖ
    have h2 := Ring.ordFrac_irreducible (K := Y.functionField) hϖ'
    obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq (R := Y.presheaf.stalk (j (genericPoint T)))
      _ _ (h2.trans h1.symm)
    have hirr : Irreducible ϖ := by
      have hassoc : Associated ϖ' ϖ := by
        refine ⟨u, IsFractionRing.injective _ Y.functionField ?_⟩
        rw [map_mul, ← hu, Units.smul_def, Algebra.smul_def, mul_comm]
      exact hassoc.irreducible hϖ'
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hirr
  -- `dϖ ∧ dx` generates `Ω²_{𝒪_{Y,P}}`
  have hspan := span_D_pair_eq_top_of_uniformizer k₀ hm hx
  have hσ := span_ιMulti_eq_top_of_span_pair k₀ hspan
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (d := 2)
    (by rw [hdim]; rfl)
  have hxE : j (genericPoint T) ∈ P.support := by
    rw [hP, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have h0 := ordForm_formPow_topFormsMap_eq_zero (sX := sY) hd hσ P hxE 1
  have hσω : topFormsMap k₀ (Y.presheaf.stalk (j (genericPoint T))) Y.functionField 2
      (exteriorPower.ιMulti _ 2 ![D k₀ _ ϖ, D k₀ _ x]) =
      exteriorPower.ιMulti Y.functionField 2 (Fin.cons (D k₀ Y.functionField (algebraMap _ _ ϖ))
        fun _ : Fin 1 => D k₀ Y.functionField (algebraMap _ _ x)) := by
    rw [topFormsMap_ιMulti]
    congr 1
    ext i
    fin_cases i <;> simp [KaehlerDifferential.map_D]
  rw [hσω] at h0
  have hω0 : exteriorPower.ιMulti Y.functionField 2 (Fin.cons (D k₀ Y.functionField
      (algebraMap _ _ ϖ)) fun _ : Fin 1 => D k₀ Y.functionField (algebraMap _ _ x)) ≠ 0 := by
    rw [← hσω]
    obtain ⟨b⟩ := exists_basis_topForms (sX := sY) (d := 2) (by rw [hdim]; norm_cast)
    have : Nontrivial (⋀[Y.functionField]^2 Ω[Y.functionField⁄k₀]) := ⟨⟨b (), 0, b.ne_zero ()⟩⟩
    exact topFormsMap_ne_zero_of_span_eq_top hσ
  rw [hτ, formPow_smul, pow_one]
  have h1 := ordForm_smul_formPow (sX := sY) (by rw [hdim]; rfl) P hω0 (inv_ne_zero hϖ0) 1
    _ rfl _ rfl
  erw [h1, h0]
  rw [show (algebraMap _ Y.functionField ϖ)⁻¹ = (algebraMap _ Y.functionField ϖ) ^ (-1 : ℤ)
    from (zpow_neg_one _).symm, MMP.Mori.ord_zpow _ hϖ0, ← hP, hϖ]
  norm_num

end BisectionB13

/-- **General fibres of the bisection case.** Over a nonempty open subset of `T`, every closed
fibre of `g` is a prime divisor `E` contained in the smooth locus of `V`, and the curve `E` is a
projective line: `(E · E) = 0`, and `(K · E) = -2` because the bisection `P` has degree two over
`T` while `(K + B) · E = 0`. -/
private theorem exists_open_good_fibre
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T]
    (hdimV : topologicalKrullDim V = 2) (hQ : IsQFactorial sV)
    (K : Divisor V) (hK : K.IsCanonicalDivisor sV 2)
    (B : QDivisor V) (hlc : MMP.Intersection.IsLogCanonicalPair sV B)
    (ε : ℚ) (hε : 0 < ε ∧ ε < 1)
    (g : V ⟶ T) [IsDominant g]
    (hg : IsMoriFibreSpace sV sT K (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)) g)
    (hdimT : topologicalKrullDim T = 1)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sV g
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)))
    (P : Mori.PrimeDivisor V) (hPB : 1 ≤ B P)
    (hdP : MMP.Flips.genericFiberPointDegree g P = 2) :
    MMP.Flips.genericFiberDegree g B = 2 ∧
    ∃ U : T.Opens, genericPoint T ∈ U ∧ ∀ t ∈ U, IsClosed ({t} : Set T) →
      ∃ (E : Mori.PrimeDivisor V) (C : ProperCurve sV), C.point = E.genericPoint ∧
        g E.genericPoint = t ∧ (E.support : Set V) = g.base ⁻¹' {t} ∧
        (E.support : Set V) ⊆ Mori.smoothLocus sV ∧
        ∃ e : projectiveLine k ≅ C.scheme,
          e.hom ≫ C.ι ≫ sV = projectiveLine k ↘ Spec (.of k) := by
  classical
  have hB0 : ∀ E, 0 ≤ B E := hlc.2.1
  have : LocallyOfFiniteType sT := hg.isContraction.isNormalVariety_target.1.toLocallyOfFiniteType
  -- the generic fibre degree of `B` is at least two
  have hBdeg : 2 ≤ MMP.Flips.genericFiberDegree g B := by
    unfold MMP.Flips.genericFiberDegree
    have hPs : P ∈ B.support := by
      rw [Finsupp.mem_support_iff]; intro h; change B P = 0 at h; linarith
    calc (2 : ℚ) ≤ B.coeff P * MMP.Flips.genericFiberPointDegree g P := by
          rw [hdP]; change (2 : ℚ) ≤ B P * ((2 : ℕ) : ℚ); push_cast; linarith
      _ ≤ ∑ E ∈ B.support, B.coeff E * MMP.Flips.genericFiberPointDegree g E :=
          Finset.single_le_sum (f := fun E => B.coeff E * MMP.Flips.genericFiberPointDegree g E)
            (fun E _ => mul_nonneg (hB0 E) (by positivity)) hPs
  obtain ⟨U, hηU, hfib⟩ := exists_open_smooth_fibre sV sT hdimV hQ K hK B g hg hdimT hnum
  -- so it is two, and the general fibre is a projective line
  obtain ⟨w₀, hw₀, hw₀c⟩ := exists_isClosed_mem_of_isOpen sT U.isOpen ⟨_, hηU⟩
  obtain ⟨-, C₀, -, -, -, -, hK₀, -, hKB₀⟩ := hfib w₀ hw₀ hw₀c
  have hgfd : MMP.Flips.genericFiberDegree g B = 2 := by linarith
  refine ⟨hgfd, U, hηU, fun w hw hwc => ?_⟩
  obtain ⟨E, C, hCE', hEw, hEsupp, hEsm, -, hiso, hKB⟩ := hfib w hw hwc
  exact ⟨E, C, hCE', hEw, hEsupp, hEsm, hiso (by linarith)⟩

/-- The restriction to `N` of a function pulled back from `T` is its pull-back along `ν ≫ g`. -/
private theorem stalkMap_genericPoint_eq_functionFieldMap {V T N : Scheme.{0}} [IsIntegral V]
    [IsIntegral T] [IsIntegral N] (g : V ⟶ T) [IsDominant g] (ν : N ⟶ V) [IsDominant (ν ≫ g)]
    (b : T.functionField) (a : V.presheaf.stalk (ν (genericPoint N)))
    (ha : algebraMap _ V.functionField a = functionFieldMap g b) :
    (ν.stalkMap (genericPoint N)).hom a = functionFieldMap (ν ≫ g) b := by
  have hgη : g (ν (genericPoint N)) = genericPoint T := by
    rw [← Scheme.Hom.comp_apply, map_genericPoint_of_isDominant]
  obtain ⟨c, hc1, hc2⟩ := exists_stalk_eq_functionFieldMap g ν hgη b
  have : a = c := IsFractionRing.injective _ V.functionField (ha.trans hc1.symm)
  rw [this, hc2]

/-- The `k`-structure is compatible with generization and stalk maps at the generic point. -/
private theorem stalkMap_stalkSpecializes_algebraMap {k : Type} [Field k] {V N : Scheme.{0}}
    [IsIntegral N] (sV : V ⟶ Spec (.of k)) (ν : N ⟶ V) {y : V}
    (hsp : ν (genericPoint N) ⤳ y) (c : k) :
    letI := stalkAlgebra sV y
    letI := functionFieldAlgebra (ν ≫ sV)
    (ν.stalkMap (genericPoint N)).hom ((V.presheaf.stalkSpecializes hsp).hom
      (algebraMap k _ c)) = algebraMap k N.functionField c := by
  letI := stalkAlgebra sV y
  letI := stalkAlgebra sV (ν (genericPoint N))
  letI := (V.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have : IsScalarTower k (V.presheaf.stalk y) (V.presheaf.stalk (ν (genericPoint N))) :=
    MMP.Threefold.Resolution.isScalarTower_stalkSpecializes sV hsp
  have h1 : (V.presheaf.stalkSpecializes hsp).hom (algebraMap k _ c) =
      algebraMap k (V.presheaf.stalk (ν (genericPoint N))) c :=
    (IsScalarTower.algebraMap_apply k (V.presheaf.stalk y) _ c).symm
  rw [h1]
  exact stalkMap_algebraMap sV ν (genericPoint N) c

/-- **Values of a regular function along the bisection.** Let `f₀ ∈ 𝒪_{V,P}` be regular at a
closed point `y` of `V`. Then the restriction of `f₀` to `N` is congruent to the value `f(y)` at
every point `z` of `N` over `y`. -/
private theorem exists_value_of_regular {k : Type} [Field k] [IsAlgClosed k] {V N : Scheme.{0}}
    (sV : V ⟶ Spec (.of k)) [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [LocallyOfFiniteType sV] [IsIntegral N] [IsLocallyNoetherian N] [IsNormal N] (ν : N ⟶ V) (f₀ : V.presheaf.stalk (ν (genericPoint N)))
    {y : V} (hyc : IsClosed ({y} : Set V)) (hsp : ν (genericPoint N) ⤳ y)
    (hreg : ∀ E : Mori.PrimeDivisor V, y ∈ E.support →
      0 ≤ V.ord (algebraMap _ V.functionField f₀) E.genericPoint)
    (hf0 : algebraMap _ V.functionField f₀ ≠ 0) :
    letI := functionFieldAlgebra (ν ≫ sV)
    ∃ c₀ : k, ∀ z : N, ν z = y → ∃ a ∈ IsLocalRing.maximalIdeal (N.presheaf.stalk z),
      algebraMap _ N.functionField a = (ν.stalkMap (genericPoint N)).hom f₀ -
        algebraMap k N.functionField c₀ := by
  letI := stalkAlgebra sV y
  letI := functionFieldAlgebra (ν ≫ sV)
  obtain ⟨a, ha⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
    y hf0 hreg
  have hsa : (V.presheaf.stalkSpecializes hsp).hom a = f₀ := by
    apply IsFractionRing.injective _ V.functionField
    rw [MMP.Mori.algebraMap_stalkSpecializes hsp, ha]
  obtain ⟨c₀, hc₀⟩ := exists_sub_algebraMap_mem_maximalIdeal sV hyc a
  refine ⟨c₀, fun z hz => ?_⟩
  subst hz
  obtain ⟨b, hb, hbe⟩ := exists_mem_maximalIdeal_of_sub_mem ν z hsp hc₀
  refine ⟨b, hb, ?_⟩
  rw [hbe, hsa, stalkMap_stalkSpecializes_algebraMap sV ν hsp c₀]

/-- **The normalization of a horizontal prime divisor.** For a finite `ν : N ⟶ V` onto a prime
divisor `P` of a surface over a curve `T`, dominating `T`: `N` is a curve, its closed points lie
over closed points of `T`, and the fibres of `N ⟶ T` over points are finite. -/
private theorem normalization_facts {k : Type} [Field k] [CharZero k] {V T N : Scheme.{0}}
    (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k)) [IsIntegral V] [IsLocallyNoetherian V]
    [LocallyOfFiniteType sV] [QuasiCompact sV] [IsIntegral T] [LocallyOfFiniteType sT]
    [CompactSpace T]
    (hdimV : topologicalKrullDim V = 2) (hdimT : topologicalKrullDim T = 1)
    (g : V ⟶ T) [IsDominant g] [IsProper g] (hgs : g ≫ sT = sV)
    [IsIntegral N] [IsLocallyNoetherian N] [IsNormal N] (ν : N ⟶ V) [IsFinite ν]
    [IsDominant (ν ≫ g)] (P : Mori.PrimeDivisor V) (hrange : Set.range ν.base = (P.support : Set V)) :
    topologicalKrullDim N = 1 ∧ (∀ Q : Mori.PrimeDivisor N, (ν ≫ g) Q.genericPoint ≠ genericPoint T) ∧
      ∀ t : T, {Q : Mori.PrimeDivisor N | (ν ≫ g) Q.genericPoint = t}.Finite := by
  classical
  let := functionFieldAlgebra sT
  let := functionFieldAlgebra (ν ≫ sV)
  have hφs : (ν ≫ g) ≫ sT = ν ≫ sV := by rw [Category.assoc, hgs]
  obtain ⟨s, hs⟩ := exists_D_ne_zero (sT := sT) (d := 0) (by rw [hdimT]; rfl)
  have hsN := D_functionFieldMap_ne_zero sT (ν ≫ sV) (ν ≫ g) hφs hs
  have hdimN : topologicalKrullDim N = 1 := by
    have h1 : topologicalKrullDim N ≤ 1 := by
      have h := topologicalKrullDim_le_of_isFinite ν (T := (P.support : Set V))
        (fun y => hrange ▸ ⟨y, rfl⟩)
      have h2 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sV P.genericPoint
      rw [P.coheight_genericPoint, hdimV] at h2
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
      refine h.trans ?_
      generalize topologicalKrullDim (closure {P.genericPoint} : Set V) = d at h2 ⊢
      induction d using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe e =>
        have h3 : ((e + 1 : ℕ∞) : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := by
          rw [WithBot.coe_add]; exact h2
        have h4 : e + 1 = 2 := WithBot.coe_injective h3
        have h5 : e = 1 :=
          WithTop.add_right_cancel ENat.one_ne_top (h4.trans one_add_one_eq_two.symm)
        rw [h5]; rfl
    have h2 := topologicalKrullDim_eq_toNat_trdeg (ν ≫ sV)
    have := essFiniteType_functionField (sX := ν ≫ sV)
    have hd1 : 1 ≤ (Algebra.trdeg k N.functionField).toNat := by
      rw [← finrank_kaehlerDifferential_eq_trdeg]
      exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hsN⟩
    rw [h2] at h1 ⊢
    have h3 : (Algebra.trdeg k N.functionField).toNat ≤ 1 := by exact_mod_cast h1
    have h4 : (Algebra.trdeg k N.functionField).toNat = 1 := le_antisymm h3 hd1
    rw [h4]; rfl
  have : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace (ν ≫ sV)
  have : IsProper (ν ≫ g) := inferInstance
  have hcl0 : ∀ Q : Mori.PrimeDivisor N, (ν ≫ g) Q.genericPoint ≠ genericPoint T := by
    intro Q h
    have hQc : IsClosed ({Q.genericPoint} : Set N) :=
      isClosed_singleton_of_ne_genericPoint (ν ≫ sV) hdimN
        (PrimeDivisor.genericPoint_ne_genericPoint Q)
    have := (ν ≫ g).isClosedMap _ hQc
    rw [Set.image_singleton, h] at this
    exact not_isClosed_genericPoint hdimT this
  refine ⟨hdimN, hcl0, fun t => ?_⟩
  have : IsNoetherian N := {}
  by_cases ht : t = genericPoint T
  · subst ht
    convert Set.finite_empty
    ext Q
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact hcl0 Q
  have hfibcl : IsClosed ((ν ≫ g).base ⁻¹' {t}) :=
    (isClosed_singleton_of_ne_genericPoint sT hdimT ht).preimage (ν ≫ g).continuous
  have hfin : ((ν ≫ g).base ⁻¹' {t}).Finite := by
    refine finite_of_isClosed_of_forall_isClosed hfibcl fun z hz => ?_
    refine isClosed_singleton_of_ne_genericPoint (ν ≫ sV) hdimN fun h => ht ?_
    have hz' : (ν ≫ g) z = t := hz
    rw [h, map_genericPoint_of_isDominant] at hz'
    exact hz'.symm
  exact (hfin.preimage AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn).subset
    fun Q hQ => hQ

open Classical in
/-- **The deck involution fixes the residues of adjoint forms of the bisection.** Let `P` be a
horizontal bisection with normalization `ν : N ⟶ V`, `Ω` a nonzero rational `m`-canonical form
(`m` even) with a pole of order `m` along `P` and neither zero nor pole along the other
horizontal prime divisors, and `ρ` its residue along `ν`. Every automorphism `σ` of `k(N)` over
`k(T)` fixes `ρ`.

Write `ρ = θ (dx̄)^{⊗m}` with `x̄` pulled back from `T`. If `σθ ≠ θ`, choose a general closed
point `x` of `N`, over a general point `t` of `T`, and the point `x'` dominated by `v_x ∘ σ`. At
`ν x` and `ν x'` the function `θ` has a common value: if `ν x = ν x'` because `θ` is the
restriction of a function regular at `ν x`, otherwise by `exists_const_of_fibre` on the fibre
over `t`, a projective line meeting `P` in the two points. Then `σθ - θ` vanishes at `x`. -/
private theorem pluriformPullback_eq_of_bisection
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T]
    (hdimV : topologicalKrullDim V = 2) (hQ : IsQFactorial sV)
    (K : Divisor V) (hK : K.IsCanonicalDivisor sV 2)
    (B : QDivisor V) (hlc : MMP.Intersection.IsLogCanonicalPair sV B)
    (ε : ℚ) (hε : 0 < ε ∧ ε < 1)
    (hklt : IsKltPair sV (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))
    (g : V ⟶ T) [IsDominant g]
    (hg : IsMoriFibreSpace sV sT K (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)) g)
    (hdimT : topologicalKrullDim T = 1)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sV g
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)))
    (P : Mori.PrimeDivisor V) (hPh : g P.genericPoint = genericPoint T) (hPB : 1 ≤ B P)
    (hdP : MMP.Flips.genericFiberPointDegree g P = 2)
    (N : Scheme.{0}) [IsIntegral N] [IsLocallyNoetherian N] [IsNormal N] (ν : N ⟶ V)
    [IsDominant (ν ≫ g)] [IsFinite ν] (hrange : Set.range ν.base = (P.support : Set V))
    (hres : IsIso (ν.residueFieldMap (genericPoint N)))
    {m : ℕ} (hm : 0 < m) (hme : Even m) (Ω : RationalPluriForms sV 2 m) (hΩ0 : Ω ≠ 0)
    (hΩh : ∀ Γ : Mori.PrimeDivisor V, g Γ.genericPoint = genericPoint T →
      Γ.ordForm Ω = -(m : ℤ) * (if Γ = P then 1 else 0))
    {ρ : RationalPluriForms (ν ≫ sV) 1 m} (hρ : IsPoincareResidue sV ν 1 m Ω ρ)
    (σ : FunctionFieldEquiv (ν ≫ sV) (ν ≫ sV))
    (hσ : ∀ a, σ (functionFieldMap (ν ≫ g) a) = functionFieldMap (ν ≫ g) a) :
    pluriformPullback (ν ≫ sV) (ν ≫ sV) (FunctionFieldEquiv.toHom (ν ≫ sV) (ν ≫ sV) σ) 1 m ρ =
      ρ := by
  classical
  obtain ⟨hVv, hVproj⟩ := (Mori.isProjectiveVariety_iff k sV).mp hg.isProjectiveVariety
  have : IsProper sV := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hVproj).2
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have : IsSeparated sV := hVv.toIsSeparated
  have hgc := hg.isContraction
  obtain ⟨hTv, hTn⟩ := hgc.isNormalVariety_target
  have : IsNormal T := hTn
  have : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  have : IsSeparated sT := hTv.toIsSeparated
  have : QuasiCompact sT := hTv.toQuasiCompact
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsProper g :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hgc.isProjectiveMorphism).2
  have hirr := isIrreducible_fibre_of_isMoriFibreSpace sV sT hdimV hQ hg hdimT
  have hdomη : g (genericPoint V) = genericPoint T := map_genericPoint_of_isDominant g
  let := functionFieldAlgebra sV
  let := functionFieldAlgebra sT
  let := functionFieldAlgebra (ν ≫ sV)
  have hη := map_genericPoint_eq_of_range_eq ν P hrange
  have hφs : (ν ≫ g) ≫ sT = ν ≫ sV := by rw [Category.assoc, hgc.comp_eq]
  have : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace (ν ≫ sV)
  have hsurjν := stalkMap_surjective_of_isIso_residueFieldMap hres
  -- a function on `T` with nonzero differential, and its pull-backs
  obtain ⟨s, hs⟩ := exists_D_ne_zero (sT := sT) (d := 0) (by rw [hdimT]; rfl)
  have hsV := D_functionFieldMap_ne_zero sT sV g hgc.comp_eq hs
  have hsN := D_functionFieldMap_ne_zero sT (ν ≫ sV) (ν ≫ g) hφs hs
  obtain ⟨hdimN, -, -⟩ := normalization_facts sV sT hdimV hdimT g hgc.comp_eq ν P hrange
  have hNv : IsNormalVariety k (ν ≫ sV) := ⟨⟨⟩, inferInstance⟩
  have hcl : ∀ y : T, y ≠ genericPoint T → IsClosed ({y} : Set T) := fun y hy =>
    isClosed_singleton_of_ne_genericPoint sT hdimT hy
  have hclN : ∀ y : N, y ≠ genericPoint N → IsClosed ({y} : Set N) := fun y hy =>
    isClosed_singleton_of_ne_genericPoint (ν ≫ sV) hdimN hy
  -- the coordinate `θ` of `ρ` along `(dx̄)^{⊗m}`
  set xbar := functionFieldMap (ν ≫ g) s with hxbar
  have hι0 : exteriorPower.ιMulti N.functionField 1 (fun _ : Fin 1 =>
      KaehlerDifferential.D k N.functionField xbar) ≠ 0 := ιMulti_fin_one_ne_zero hsN
  obtain ⟨bN⟩ := exists_basis_topForms (sX := ν ≫ sV) (d := 1) (by rw [hdimN]; norm_cast)
  obtain ⟨ωN, hωN⟩ : ∃ ω : RationalPluriForms (ν ≫ sV) 1 m, ω = formPow
      (exteriorPower.ιMulti N.functionField 1 fun _ : Fin 1 =>
        KaehlerDifferential.D k N.functionField xbar) m := ⟨_, rfl⟩
  have hωN0 : ωN ≠ 0 := hωN ▸ formPow_ne_zero_of_ne_zero (sX := ν ≫ sV) hdimN hι0 m
  have hrepr0 : (ZTensorPower.basis bN m).repr ωN () ≠ 0 :=
    MMP.Mori.repr_ne_zero_of_ne_zero bN hωN0
  set θ := (ZTensorPower.basis bN m).repr ρ () / (ZTensorPower.basis bN m).repr ωN ()
    with hθdef
  have hρθ : ρ = θ • ωN := eq_div_repr_smul bN ρ ωN hrepr0
  have hσx : FunctionFieldEquiv.toHom (ν ≫ sV) (ν ≫ sV) σ xbar = xbar := hσ s
  rw [hρθ, hωN]
  erw [pluriformPullback_smul_formPow_D (ν ≫ sV) (ν ≫ sV) hdimN hdimN _ xbar θ hsN m]
  rw [hσx]
  congr 1
  change σ θ = θ
  by_contra hδ
  have hδ0 : σ θ - θ ≠ 0 := sub_ne_zero.mpr hδ
  have hθ0 : θ ≠ 0 := by rintro h0; apply hδ; rw [h0, map_zero]
  have : IsNoetherian V := {}
  -- the lift `f₀ ∈ 𝒪_{V,P}` of `θ`
  obtain ⟨f₀, hf₀⟩ := hsurjν θ
  set f := algebraMap (V.presheaf.stalk (ν (genericPoint N))) V.functionField f₀ with hfdef
  have hf0 : f ≠ 0 := by
    intro h0
    have : f₀ = 0 := IsFractionRing.injective _ V.functionField (by rw [← hfdef, h0, map_zero])
    apply hθ0; rw [← hf₀, this, map_zero]
  have hfP : 0 ≤ V.ord f P.genericPoint := by
    have hcoh : Order.coheight (ν (genericPoint N)) = 1 := by
      rw [hη]; exact P.coheight_genericPoint
    have : IsDiscreteValuationRing (V.presheaf.stalk (ν (genericPoint N))) := by
      rw [hη]; exact P.isDiscreteValuationRing_localRing
    have h := zero_le_ord_algebraMap hcoh (a := f₀) (by rintro rfl; exact hf0 (map_zero _))
    exact h.trans_eq (congrArg (fun y => V.ord f y) hη)
  -- the finitely many bad prime divisors of `V`
  obtain ⟨φf, hφf⟩ := MMP.Positivity.exists_units_of_ne_zero hf0
  set Zf : Set (Mori.PrimeDivisor V) := {E | V.ord f E.genericPoint ≠ 0} with hZfdef
  have hZf : Zf.Finite := (finite_ord_ne_zero φf).subset fun E hE => by
    change Mori.PrimeDivisor.ord E φf ≠ 0; rw [hφf]; exact hE
  obtain ⟨Zμ, hZμ, hμ⟩ := exists_finite_ord_le_one sV hdimV hsV
  set ZE : Set (Mori.PrimeDivisor V) :=
    {E | E.ordForm Ω ≠ 0} ∪ Zf ∪ Zμ with hZEdef
  have hZE : ZE.Finite := ((finite_ordForm_ne_zero Ω).union hZf).union hZμ
  -- the points of `P` on the other polar divisors of `f`
  set ZP : Set V := {y | y ∈ P.support ∧ ∃ E ∈ Zf, E ≠ P ∧ y ∈ E.support} with hZPdef
  have hZP : ZP.Finite := by
    have hsub : ZP ⊆ ⋃ E ∈ Zf \ {P}, (P.support : Set V) ∩ E.support := fun y hy => by
      obtain ⟨hyP, E, hE, hEP, hyE⟩ := hy
      exact Set.mem_iUnion₂.mpr ⟨E, ⟨hE, hEP⟩, hyP, hyE⟩
    refine ((hZf.diff).biUnion fun E hE => ?_).subset hsub
    refine finite_of_isClosed_of_forall_isClosed
      (P.idealSheaf.support.isClosed.inter E.idealSheaf.support.isClosed) fun z hz => ?_
    refine isClosed_singleton_of_mem_support sV hdimV P hz.1 fun h => hE.2 ?_
    exact (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E P (h ▸ hz.2))
  -- the finitely many bad points of `T`
  set τs : RationalPluriForms sT 1 ((1 : ℕ) : ℤ) := formPow (exteriorPower.ιMulti T.functionField 1
    fun _ : Fin 1 => KaehlerDifferential.D k T.functionField s) 1 with hτsdef
  have hs0 : s ≠ 0 := by rintro rfl; exact hs (map_zero _)
  set ZT : Set T := ((fun E : Mori.PrimeDivisor V => g E.genericPoint) ''
      {E | E ∈ ZE ∧ g E.genericPoint ≠ genericPoint T}) ∪ g.base '' ZP ∪
      {t | T.ord s t ≠ 0} ∪
      ((fun R : Mori.PrimeDivisor T => R.genericPoint) '' {R | R.ordForm τs ≠ 0}) with hZTdef
  have hZT : ZT.Finite :=
    (((hZE.subset fun E hE => hE.1).image _).union (hZP.image _)).union
      (finite_setOf_ord_ne_zero hs0) |>.union ((finite_ordForm_ne_zero τs).image _)
  have hηZT : genericPoint T ∉ ZT := by
    rintro (((⟨E, ⟨-, hE⟩, hEη⟩ | ⟨y, hy, hyη⟩) | hη') | ⟨R, -, hRη⟩)
    · exact hE hEη
    · -- `y` is a closed point of `P`
      obtain ⟨hyP, E, hE, hEP, hyE⟩ := hy
      have hyc : IsClosed ({y} : Set V) := isClosed_singleton_of_mem_support sV hdimV P hyP
        fun h => hEP (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E P
          (h ▸ hyE))
      have := g.isClosedMap _ hyc
      rw [Set.image_singleton, hyη] at this
      exact not_isClosed_genericPoint hdimT this
    · apply hη'
      refine Scheme.ord_eq_zero_of_coheight_neq_one ?_ _
      rw [Order.coheight_eq_zero.mpr fun y _ => (genericPoint_spec T).specializes trivial]
      simp
    · exact PrimeDivisor.genericPoint_ne_genericPoint R hRη
  have hZTcl : IsClosed ZT := isClosed_of_finite_of_forall hZT fun y hy =>
    hcl y fun h => hηZT (h ▸ hy)
  obtain ⟨-, U₁, hηU₁, hU₁⟩ := exists_open_good_fibre sV sT hdimV hQ K hK B hlc ε hε g hg
    hdimT hnum P hPB hdP
  -- a general closed point `x` of `N`
  set δ := σ θ - θ with hδdef
  have hZN : {x : N | N.ord δ x ≠ 0}.Finite := finite_setOf_ord_ne_zero hδ0
  have hZNcl : IsClosed {x : N | N.ord δ x ≠ 0} := isClosed_of_finite_of_forall hZN fun y hy =>
    hclN y fun h => hy (by
      rw [h]
      refine Scheme.ord_eq_zero_of_coheight_neq_one ?_ _
      rw [Order.coheight_eq_zero.mpr fun y _ => (genericPoint_spec N).specializes trivial]
      simp)
  set W : Set N := (ν ≫ g).base ⁻¹' ((U₁ : Set T) ∩ ZTᶜ) ∩ {x : N | N.ord δ x ≠ 0}ᶜ with hWdef
  have hWo : IsOpen W :=
    ((U₁.isOpen.inter hZTcl.isOpen_compl).preimage (ν ≫ g).continuous).inter hZNcl.isOpen_compl
  have hηW : genericPoint N ∈ W := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change (ν ≫ g) (genericPoint N) ∈ U₁
      rw [map_genericPoint_of_isDominant]; exact hηU₁
    · change (ν ≫ g) (genericPoint N) ∉ ZT
      rw [map_genericPoint_of_isDominant]; exact hηZT
    · intro h; apply h
      refine Scheme.ord_eq_zero_of_coheight_neq_one ?_ _
      rw [Order.coheight_eq_zero.mpr fun y _ => (genericPoint_spec N).specializes trivial]
      simp
  obtain ⟨x, hxW, hxc⟩ := exists_isClosed_mem_of_isOpen (ν ≫ sV) hWo ⟨_, hηW⟩
  have hxη : x ≠ genericPoint N := fun h => not_isClosed_genericPoint hdimN (h ▸ hxc)
  obtain ⟨Q, rfl⟩ : ∃ Q : Mori.PrimeDivisor N, Q.genericPoint = x :=
    ⟨_, AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x
      (coheight_eq_one_of_ne_genericPoint hdimN hxη)⟩
  obtain ⟨⟨htU₁, htZT⟩, hδx⟩ := hxW
  change (ν ≫ g) Q.genericPoint ∈ U₁ at htU₁
  change (ν ≫ g) Q.genericPoint ∉ ZT at htZT
  have hδx' : N.ord δ Q.genericPoint = 0 := by simpa using hδx
  -- the point `t` of `T` below `x`, and the point `x'` dominated by `v_x ∘ σ`
  obtain ⟨x', hdom, hx't⟩ := exists_dominates_comap (ν ≫ g) σ hσ Q
  obtain ⟨t, htdef⟩ : ∃ t : T, (ν ≫ g) Q.genericPoint = t := ⟨_, rfl⟩
  rw [htdef] at htU₁ htZT hx't
  have htc : IsClosed ({t} : Set T) := by
    have := (ν ≫ g).isClosedMap _ hxc
    rwa [Set.image_singleton, htdef] at this
  have htη : t ≠ genericPoint T := fun h => not_isClosed_genericPoint hdimT (h ▸ htc)
  -- the good fibre over `t`
  obtain ⟨E, C, hCE, hEt, hEsupp, hEsm, e, he⟩ := hU₁ t htU₁ htc
  have hEv : g E.genericPoint ≠ genericPoint T := by rw [hEt]; exact htη
  have hPE : P ≠ E := fun h => hEv (h ▸ hPh)
  have hEZ : E ∉ ZE := fun h => htZT (Or.inl (Or.inl (Or.inl ⟨E, ⟨h, hEv⟩, hEt⟩)))
  simp only [hZEdef, hZfdef, Set.mem_union, Set.mem_setOf_eq, not_or, ne_eq, not_not] at hEZ
  obtain ⟨⟨hΩE, hfE⟩, hEμ⟩ := hEZ
  -- the vertical prime divisors meeting `E` are `E`
  have hvert : ∀ E' : Mori.PrimeDivisor V, g E'.genericPoint ≠ genericPoint T →
      ∀ y ∈ E.support, y ∈ E'.support → E' = E := by
    intro E' hE'v y hyE hyE'
    have hgy : g y = t := by
      have : y ∈ g.base ⁻¹' {t} := hEsupp ▸ hyE
      exact this
    have hgy' : g y = g E'.genericPoint := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE'
      have h1 := (specializes_iff_mem_closure.mpr hyE').map g.continuous
      have h2 := specializes_iff_mem_closure.mp h1
      rwa [(hcl _ hE'v).closure_eq] at h2
    exact primeDivisor_eq_of_map_genericPoint_eq g hirr E' E htc (hgy' ▸ hgy) hEt htη hdomη
  -- the value of `s` at `t` and the local parameter `π = s - s(t)`
  obtain ⟨Rt, rfl⟩ : ∃ R : Mori.PrimeDivisor T, R.genericPoint = t :=
    ⟨_, AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne t
      (coheight_eq_one_of_ne_genericPoint hdimT htη)⟩
  letI := stalkAlgebra sT Rt.genericPoint
  haveI := isScalarTower_stalk_functionField sT Rt.genericPoint
  have hst : T.ord s Rt.genericPoint = 0 := by
    by_contra h; exact htZT (Or.inl (Or.inr h))
  obtain ⟨bt, hbt⟩ : s ∈ (algebraMap Rt.localRing T.functionField).range := by
    rw [← Rt.divisorialValuation_le_one_iff, ← zero_le_ord_iff Rt hs0, hst]
  obtain ⟨ct, hct⟩ := exists_sub_algebraMap_mem_maximalIdeal sT htc bt
  set π := s - algebraMap k T.functionField ct with hπdef
  have hπ : π = algebraMap Rt.localRing T.functionField (bt - algebraMap k _ ct) := by
    rw [map_sub, hbt, ← IsScalarTower.algebraMap_apply]
  have hDπ : KaehlerDifferential.D k T.functionField π = KaehlerDifferential.D k T.functionField s := by
    rw [hπdef, map_sub, Derivation.map_algebraMap, sub_zero]
  have hπ0 : π ≠ 0 := by
    intro h0; apply hs; rw [← hDπ, h0, map_zero]
  have hπ1 : T.ord π Rt.genericPoint = 1 := by
    have h1 : 1 ≤ T.ord π Rt.genericPoint := by
      rw [hπ]; exact one_le_ord_algebraMap_of_mem Rt hct (hπ ▸ hπ0)
    have hds : Rt.ordForm τs = 0 := by
      by_contra h; exact htZT (Or.inr ⟨Rt, h, rfl⟩)
    have h2 := ord_sub_one_le_ordForm_d hdimT Rt (bt - algebraMap k _ ct) τs (by
      rw [hτsdef, ← hπ, hDπ]) (hτsdef ▸ formPow_ne_zero_of_ne_zero (sX := sT) hdimT
        (ιMulti_fin_one_ne_zero hs) 1)
    rw [← hπ, hds] at h2
    omega
  -- the pull-back `u = g^*π`
  set u := functionFieldMap g π with hudef
  have hu00 : u ≠ 0 := (map_ne_zero _).mpr hπ0
  have hu1 : V.ord u E.genericPoint = 1 := by
    obtain ⟨b', hb', hb'm⟩ : ∃ b' : T.presheaf.stalk (g E.genericPoint),
        algebraMap _ T.functionField b' = π ∧ b' ∈ IsLocalRing.maximalIdeal _ := by
      rw [hEt]; exact ⟨_, hπ.symm, hct⟩
    have hua : u = algebraMap E.localRing V.functionField ((g.stalkMap E.genericPoint).hom b') := by
      rw [hudef, ← hb', MMP.Mori.functionFieldMap_algebraMap_stalk]
    have hm1 : (g.stalkMap E.genericPoint).hom b' ∈ IsLocalRing.maximalIdeal E.localRing :=
      (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
        (IsLocalRing.mem_maximalIdeal _).mp hb'm ((isUnit_map_iff _ _).mp hu)
    have h1 := one_le_ord_algebraMap_of_mem E hm1 (hua ▸ hu00)
    have hD : KaehlerDifferential.D k V.functionField
        (algebraMap E.localRing V.functionField ((g.stalkMap E.genericPoint).hom b')) =
        KaehlerDifferential.D k V.functionField (functionFieldMap g s) := by
      rw [← hua, hudef, hπdef, map_sub, map_sub]
      rw [show functionFieldMap g (algebraMap k T.functionField ct) =
        algebraMap k V.functionField ct from
          (functionFieldHomOfEq_apply sV sT g hgc.comp_eq _).symm.trans
            ((functionFieldHomOfEq sV sT g hgc.comp_eq).commutes ct)]
      rw [Derivation.map_algebraMap, sub_zero]
    have h2 := hμ E hEμ _ hD (hua ▸ hu00)
    rw [← hua] at h1 h2
    omega
  have hu0 : ∀ E' : Mori.PrimeDivisor V, E' ≠ E → ∀ y ∈ E.support, y ∈ E'.support →
      V.ord u E'.genericPoint = 0 := by
    intro E' hE' y hyE hyE'
    by_cases hE'h : g E'.genericPoint = genericPoint T
    · exact ord_functionFieldMap_eq_zero g E' hE'h hπ0
    · exact absurd (hvert E' hE'h y hyE hyE') hE'
  have hΩP : P.ordForm Ω = -(m : ℤ) := by have := hΩh P hPh; simpa using this
  have hΩ' : ∀ E' : Mori.PrimeDivisor V, E' ≠ P → ∀ y ∈ E.support, y ∈ E'.support →
      E'.ordForm Ω = 0 := by
    intro E' hE'P y hyE hyE'
    by_cases hE'h : g E'.genericPoint = genericPoint T
    · rw [hΩh E' hE'h, if_neg hE'P, mul_zero]
    · rw [hvert E' hE'h y hyE hyE']; exact hΩE
  -- the two points of `P` below `x` and `x'`
  have hyP : ν Q.genericPoint ∈ P.support := hrange ▸ ⟨_, rfl⟩
  have hy'P : ν x' ∈ P.support := hrange ▸ ⟨_, rfl⟩
  have hyE : ν Q.genericPoint ∈ E.support := by
    rw [hEsupp]; exact htdef
  have hy'E : ν x' ∈ E.support := by
    rw [hEsupp]; exact hx't
  have hsp : ∀ z : N, ν (genericPoint N) ⤳ ν z := fun z =>
    ((genericPoint_spec N).specializes trivial).map ν.continuous
  -- a common value of `θ` at `x` and `x'`
  obtain ⟨c₀, ⟨a, ha, hae⟩, ⟨a', ha', hae'⟩⟩ : ∃ c₀ : k,
      (∃ a ∈ IsLocalRing.maximalIdeal (N.presheaf.stalk Q.genericPoint),
        algebraMap _ N.functionField a = θ - algebraMap k N.functionField c₀) ∧
      (∃ a ∈ IsLocalRing.maximalIdeal (N.presheaf.stalk x'),
        algebraMap _ N.functionField a = θ - algebraMap k N.functionField c₀) := by
    by_cases hyy : ν Q.genericPoint = ν x'
    · -- `θ` is the restriction of `f`, regular at `ν x`
      have hyc : IsClosed ({ν Q.genericPoint} : Set V) :=
        isClosed_singleton_of_mem_support sV hdimV E hyE fun h => hPE
          (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support P E (h ▸ hyP))
      have hreg : ∀ E' : Mori.PrimeDivisor V, ν Q.genericPoint ∈ E'.support →
          0 ≤ V.ord f E'.genericPoint := by
        intro E' hE'
        by_cases hE'P : E' = P
        · subst hE'P; exact hfP
        by_cases hE'h : g E'.genericPoint = genericPoint T
        · by_contra hneg
          apply htZT
          exact Or.inl (Or.inl (Or.inr ⟨ν Q.genericPoint, ⟨hyP, E', by
            simp only [hZfdef, Set.mem_setOf_eq]; omega, hE'P, hE'⟩, by
              change (ν ≫ g) Q.genericPoint = _; rw [htdef]⟩))
        · rw [hvert E' hE'h _ hyE hE', hfE]
      obtain ⟨c₀, hc₀⟩ := exists_value_of_regular sV ν f₀ hyc (hsp Q.genericPoint) hreg hf0
      rw [hf₀] at hc₀
      exact ⟨c₀, hc₀ _ rfl, hc₀ _ hyy.symm⟩
    · -- the fibre over `t` meets `P` in `ν x ≠ ν x'`
      obtain ⟨c₀, hc₀⟩ := exists_const_of_fibre hdimV E hEsm C hCE e he hu1 hu0 P hPE hm hme Ω hΩ0
        hΩP hΩ' hyP hyE hy'P hy'E hyy
      have hval : ∀ z : N, (ν z = ν Q.genericPoint ∨ ν z = ν x') →
          ∃ a ∈ IsLocalRing.maximalIdeal (N.presheaf.stalk z),
            algebraMap _ N.functionField a = θ - algebraMap k N.functionField c₀ := by
        intro z hz
        letI := stalkAlgebra sV (ν z)
        obtain ⟨p, c, uy, huy, hp1, hcu, hcc, hΩp⟩ := hc₀ (ν z) hz
        rw [← huy] at hΩp
        have hres' := residue_eq_of_presentation ν P hη hsurjν (hsp z) hp1 Ω hΩp hρ
        have hū : (ν.stalkMap (genericPoint N)).hom ((V.presheaf.stalkSpecializes (hsp z)).hom uy) =
            functionFieldMap (ν ≫ g) π :=
          stalkMap_genericPoint_eq_functionFieldMap g ν π _ (by
            rw [MMP.Mori.algebraMap_stalkSpecializes, huy])
        have hDū : KaehlerDifferential.D k N.functionField (functionFieldMap (ν ≫ g) π) =
            KaehlerDifferential.D k N.functionField xbar := by
          rw [hπdef, map_sub, map_sub,
            show functionFieldMap (ν ≫ g) (algebraMap k T.functionField ct) =
              algebraMap k N.functionField ct from
                (functionFieldHomOfEq_apply (ν ≫ sV) sT (ν ≫ g) hφs _).symm.trans
                  ((functionFieldHomOfEq (ν ≫ sV) sT (ν ≫ g) hφs).commutes ct),
            Derivation.map_algebraMap, sub_zero]
        rw [hū, hDū, ← hωN] at hres'
        have hθc : θ = (ν.stalkMap (genericPoint N)).hom
            ((V.presheaf.stalkSpecializes (hsp z)).hom c) :=
          smul_left_injective N.functionField hωN0 (hρθ.symm.trans hres')
        obtain ⟨a, ha, hae⟩ := exists_mem_maximalIdeal_of_sub_mem ν z (hsp z) hcc
        refine ⟨a, ha, ?_⟩
        rw [hae, ← hθc, stalkMap_stalkSpecializes_algebraMap sV ν (hsp z) c₀]
      exact ⟨c₀, hval _ (Or.inl rfl), hval _ (Or.inr rfl)⟩
  -- `σθ - θ` vanishes at `x`
  have hv1 : Q.divisorialValuation (θ - algebraMap k N.functionField c₀) < 1 := by
    rw [← hae]; exact (Q.divisorialValuation_algebraMap_lt_one_iff a).mpr ha
  have hv2 : Q.divisorialValuation (σ θ - algebraMap k N.functionField c₀) < 1 := by
    have h := hdom.2 a' ha'
    rw [hae', Valuation.comap_apply] at h
    change Q.divisorialValuation (σ (θ - algebraMap k N.functionField c₀)) < 1 at h
    rwa [map_sub, AlgEquiv.commutes] at h
  have hv : Q.divisorialValuation δ < 1 := by
    have : δ = (σ θ - algebraMap k N.functionField c₀) - (θ - algebraMap k N.functionField c₀) := by
      rw [hδdef]; ring
    rw [this]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv2 hv1)
  have := (one_le_ord_iff Q hδ0).mpr hv
  omega

/-- **The adjunction boundary from a residue family.** Let `ν : N ⟶ V` be a branch of the
horizontal floor and `Ω` a nonzero rational `M`-canonical form whose pull-back multiples
`g^*ψ_t · Ω` generate `ω_V^{[M]}(MB)` over `g⁻¹ W_t`, as in `exists_localGenerator_of_vertical`.
If the residues of the forms `g^*a · Ω` along `ν` are `(ν ≫ g)^*a · ρ`, then
`Θ_Q = -(ord_Q ρ + ord_Q (ν ≫ g)^*ψ_{t(Q)}) / M` is an adjunction boundary. -/
private theorem exists_adjunctionBoundary_of_residue
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k))
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [LocallyOfFiniteType sV]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    (hdimV : topologicalKrullDim V = 2) (hdimT : topologicalKrullDim T = 1) (g : V ⟶ T)
    [IsDominant g] (B : QDivisor V) (N : Scheme.{0}) [IsIntegral N] [IsLocallyNoetherian N] [IsNormal N] (ν : N ⟶ V)
    [IsDominant (ν ≫ g)] [LocallyOfFiniteType (ν ≫ sV)] [CompactSpace N]
    (hdimN : topologicalKrullDim N = 1)
    (hfib : ∀ t : T, {Q : Mori.PrimeDivisor N | (ν ≫ g) Q.genericPoint = t}.Finite)
    (hcl0 : ∀ Q : Mori.PrimeDivisor N, (ν ≫ g) Q.genericPoint ≠ genericPoint T)
    {M : ℕ} (hM : 0 < M) (Ω : RationalPluriForms sV 2 M) (hΩ0 : Ω ≠ 0)
    (ψ : T → T.functionField) (hψ0 : ∀ t, ψ t ≠ 0)
    (hψfin : {t | ψ t ≠ 1}.Finite) (W : T → T.Opens) (hW : ∀ t, t ∈ W t)
    (hgen : ∀ t (Γ : Mori.PrimeDivisor V), (Γ.support ∩ g ⁻¹ᵁ W t).Nonempty →
      (V.ord (functionFieldMap g (ψ t)) Γ.genericPoint : ℚ) + Γ.ordForm Ω + M * B Γ = 0)
    (hWord : ∀ t y, y ∈ W t → y ≠ t → T.ord (ψ t) y = 0)
    (hWψ : ∀ t y, y ∈ W t → y ≠ t → ψ y = 1)
    (ρ : RationalPluriForms (ν ≫ sV) 1 M) (hρ0 : ρ ≠ 0)
    (hres : ∀ a : T.functionField, IsPoincareResidue sV ν 1 M (functionFieldMap g a • Ω)
      (functionFieldMap (ν ≫ g) a • ρ)) :
    ∃ Θ : QDivisor N,
      (∃ m : ℕ, 0 < m ∧ ∀ x : N, ∃ U : V.Opens, ν.base x ∈ U ∧
        ∃ τ : RationalPluriForms sV 2 m, GeneratesOn B m U τ ∧
          ∃ ρ : RationalPluriForms (ν ≫ sV) 1 m, IsPoincareResidue sV ν 1 m τ ρ ∧
            GeneratesOn Θ m (ν ⁻¹ᵁ U) ρ) ∧
      ∀ Q : Mori.PrimeDivisor N, Θ Q = -((Q.ordForm ρ : ℤ) : ℚ) / M -
        (N.ord (functionFieldMap (ν ≫ g) (ψ ((ν ≫ g) Q.genericPoint))) Q.genericPoint : ℚ) / M := by
  classical
  have hd1 : topologicalKrullDim N = ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdimN
  set Θf : Mori.PrimeDivisor N → ℚ := fun Q => -((Q.ordForm ρ : ℤ) : ℚ) / M -
    (N.ord (functionFieldMap (ν ≫ g) (ψ ((ν ≫ g) Q.genericPoint))) Q.genericPoint : ℚ) / M
  have hΘfin : (Function.support Θf).Finite := by
    have hpre : {Q : Mori.PrimeDivisor N | ψ ((ν ≫ g) Q.genericPoint) ≠ 1}.Finite := by
      refine (hψfin.biUnion fun t _ => hfib t).subset fun Q hQ => ?_
      exact Set.mem_iUnion₂.mpr ⟨_, hQ, rfl⟩
    refine ((finite_ordForm_ne_zero ρ).union hpre).subset fun Q hQ => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    apply hQ
    simp only [Θf, h.1, h.2, map_one, Scheme.ord_one]
    simp
  set Θ : QDivisor N := Finsupp.ofSupportFinite Θf hΘfin
  have hΘ : ∀ Q, Θ Q = Θf Q := fun Q => rfl
  refine ⟨Θ, ⟨M, hM, fun x => ?_⟩, hΘ⟩
  set t := (ν ≫ g) x
  have hxU : ν.base x ∈ g ⁻¹ᵁ W t := hW t
  have hψt0 : functionFieldMap g (ψ t) ≠ 0 := (map_ne_zero _).mpr (hψ0 t)
  have hψt0' : functionFieldMap (ν ≫ g) (ψ t) ≠ 0 := (map_ne_zero _).mpr (hψ0 t)
  refine ⟨g ⁻¹ᵁ W t, hxU, functionFieldMap g (ψ t) • Ω, ⟨smul_ne_zero hψt0 hΩ0, ?_⟩, _,
    hres (ψ t), ⟨smul_ne_zero hψt0' hρ0, ?_⟩⟩
  · intro Γ hΓ
    have hd2 : topologicalKrullDim V = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdimV]; rfl
    rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hd2 hψt0 hΩ0]
    have := hgen t Γ hΓ
    rw [show B.coeff Γ = B Γ from rfl]
    push_cast at this ⊢
    linear_combination this
  · intro Q hQ
    rw [show Θ.coeff Q = Θf Q from rfl,
      Q.ordForm_smul_of_topologicalKrullDim_eq hd1 hψt0' hρ0]
    simp only [Θf]
    obtain ⟨y, hyQ, hyU⟩ := hQ
    have hyW : (ν ≫ g) y ∈ W t := hyU
    have hQW : (ν ≫ g) Q.genericPoint ∈ W t := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyQ
      have hsp : (ν ≫ g) Q.genericPoint ⤳ (ν ≫ g) y :=
        (specializes_iff_mem_closure.mpr hyQ).map (ν ≫ g).continuous
      exact hsp.mem_open (W t).isOpen hyW
    have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    by_cases hQt : (ν ≫ g) Q.genericPoint = t
    · rw [hQt]
      field_simp
      push_cast
      ring
    · have hψ1 := hWψ t _ hQW hQt
      have hord0 := hWord t _ hQW hQt
      obtain ⟨u, hu, hue⟩ := exists_isUnit_algebraMap_eq_of_ord_eq_zero
        (MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hdimT (hcl0 Q)) (hψ0 t) hord0
      have h0 := ord_functionFieldMap_eq_zero_of_isUnit (ν ≫ g) Q hu
      rw [hue] at h0
      rw [hψ1, map_one, Scheme.ord_one, h0]
      field_simp
      ring_nf

/-- **The residue field as the target of a surjection.** A surjective `k`-linear ring
homomorphism `φ` from a local `k`-algebra `R` to a field `K` induces `κ(R) ≃ₐ[k] K`. -/
private theorem exists_residueField_algEquiv {k R K : Type*} [Field k] [CommRing R]
    [IsLocalRing R] [Field K] [Algebra k R] [Algebra k K] (φ : R →+* K)
    (hφ : ∀ c : k, φ (algebraMap k R c) = algebraMap k K c) (hsurj : Function.Surjective φ) :
    ∃ e : IsLocalRing.ResidueField R ≃ₐ[k] K, ∀ a, e (IsLocalRing.residue R a) = φ a := by
  have hker : RingHom.ker φ = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ hsurj)
  let e₀ : R ⧸ RingHom.ker φ ≃+* K := RingHom.quotientKerEquivOfSurjective hsurj
  let e₁ : IsLocalRing.ResidueField R ≃+* R ⧸ RingHom.ker φ := Ideal.quotEquivOfEq hker.symm
  refine ⟨AlgEquiv.ofRingEquiv (f := e₁.trans e₀) fun c => ?_, fun a => rfl⟩
  change φ (algebraMap k R c) = _
  exact hφ c

/-- On a curve, every differential is a multiple of a nonzero one. -/
private theorem exists_D_eq_smul_of_ne_zero {k : Type} [Field k] [PerfectField k] {N : Scheme.{0}}
    (sN : N ⟶ Spec (.of k)) [IsIntegral N] [LocallyOfFiniteType sN]
    (hdimN : topologicalKrullDim N = 1) {x : N.functionField}
    (hx : letI := functionFieldAlgebra sN; KaehlerDifferential.D k N.functionField x ≠ 0) :
    letI := functionFieldAlgebra sN
    ∀ l : N.functionField, ∃ c : N.functionField,
      KaehlerDifferential.D k N.functionField l = c • KaehlerDifferential.D k N.functionField x := by
  letI := functionFieldAlgebra sN
  have := essFiniteType_functionField (sX := sN)
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sN) (d := 1)
    (by rw [hdimN]; rfl)
  have hr : Module.finrank N.functionField Ω[N.functionField⁄k] = 1 :=
    (finrank_kaehlerDifferential_eq_trdeg k N.functionField).trans hd
  intro l
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hx).mp hr (KaehlerDifferential.D k _ l)
  exact ⟨c, hc.symm⟩

/-- **The bisection.** The deck involution is crepant and fixes the residues of vertical
adjoint pluriforms. -/
private theorem bisection_clause
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T]
    (hdimV : topologicalKrullDim V = 2) (hQ : IsQFactorial sV)
    (K : Divisor V) (hK : K.IsCanonicalDivisor sV 2)
    (B : QDivisor V) (hlc : MMP.Intersection.IsLogCanonicalPair sV B)
    (ε : ℚ) (hε : 0 < ε ∧ ε < 1)
    (hklt : IsKltPair sV (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))
    (g : V ⟶ T) [IsDominant g]
    (hg : IsMoriFibreSpace sV sT K (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)) g)
    (hdimT : topologicalKrullDim T = 1)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sV g
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)))
    (P : Mori.PrimeDivisor V) (hH : {P' : Mori.PrimeDivisor V | ⌊B.coeff P'⌋ ≠ 0 ∧ g.base P'.genericPoint = genericPoint T} = {P})
    (hd : (letI := (g.residueFieldMap P.genericPoint).hom.toAlgebra
      Module.finrank (T.residueField (g.base P.genericPoint)) (V.residueField P.genericPoint)) = 2) :
    let IsNormalization : ∀ (P : Mori.PrimeDivisor V) (N : Scheme.{0}), (N ⟶ V) → Prop :=
      fun P N ν => IsFinite ν ∧ Set.range ν.base = (P.support : Set V) ∧
        ∃ _ : IsIntegral N, IsIso (ν.residueFieldMap (genericPoint N))
    let IsAdjunctionBoundary :
        ∀ (N : Scheme.{0}) [IsIntegral N] [IsLocallyNoetherian N] (ν : N ⟶ V), QDivisor N → Prop :=
      fun N _ _ ν Θ => ∃ m : ℕ, 0 < m ∧ ∀ x : N, ∃ U : V.Opens, ν.base x ∈ U ∧
        ∃ τ : RationalPluriForms sV 2 m, GeneratesOn B m U τ ∧
          ∃ ρ : RationalPluriForms (ν ≫ sV) 1 m, IsPoincareResidue sV ν 1 m τ ρ ∧
            GeneratesOn Θ m (ν ⁻¹ᵁ U) ρ
    let IsVerticalAdjoint : ∀ m : ℕ, RationalPluriForms sV 2 m → Prop :=
      fun m Ω => ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ φ : T.functionField,
        GeneratesOn B m (g ⁻¹ᵁ U) (functionFieldMap g φ • Ω)
      ∀ (N : Scheme.{0}) [IsIntegral N] [IsLocallyNoetherian N] [IsNormal N] (ν : N ⟶ V)
        [IsDominant (ν ≫ g)], IsNormalization P N ν →
        ∃ Θ : QDivisor N, IsAdjunctionBoundary N ν Θ ∧ ∃ m₀ : ℕ, 0 < m₀ ∧
          ∀ σ : FunctionFieldEquiv (ν ≫ sV) (ν ≫ sV),
            (∀ a, σ (functionFieldMap (ν ≫ g) a) = functionFieldMap (ν ≫ g) a) →
            IsCrepantBirationalMap (ν ≫ sV) (ν ≫ sV) Θ Θ σ ∧
            ∀ m : ℕ, m₀ ∣ m → Even m → ∀ Ω : RationalPluriForms sV 2 m, IsVerticalAdjoint m Ω →
              ∀ ρ : RationalPluriForms (ν ≫ sV) 1 m, IsPoincareResidue sV ν 1 m Ω ρ →
                pluriformPullback (ν ≫ sV) (ν ≫ sV)
                  (FunctionFieldEquiv.toHom (ν ≫ sV) (ν ≫ sV) σ) 1 m ρ = ρ := by
  classical
  intro IsNormalization IsAdjunctionBoundary IsVerticalAdjoint N _ _ _ ν _ hn
  obtain ⟨hVv, hVproj⟩ := (Mori.isProjectiveVariety_iff k sV).mp hg.isProjectiveVariety
  have : IsProper sV := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hVproj).2
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have : IsSeparated sV := hVv.toIsSeparated
  have hgc := hg.isContraction
  obtain ⟨hTv, hTn⟩ := hgc.isNormalVariety_target
  have : IsNormal T := hTn
  have : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  have : IsSeparated sT := hTv.toIsSeparated
  have : QuasiCompact sT := hTv.toQuasiCompact
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsProper g :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hgc.isProjectiveMorphism).2
  have hirr := isIrreducible_fibre_of_isMoriFibreSpace sV sT hdimV hQ hg hdimT
  have hcl : ∀ y : T, y ≠ genericPoint T → IsClosed ({y} : Set T) := fun y hy =>
    isClosed_singleton_of_ne_genericPoint sT hdimT hy
  have hB0 : ∀ E, 0 ≤ B E := hlc.2.1
  have hPH : P ∈ {P' : Mori.PrimeDivisor V |
      ⌊B.coeff P'⌋ ≠ 0 ∧ g.base P'.genericPoint = genericPoint T} := by
    rw [hH]; rfl
  have hPh : g P.genericPoint = genericPoint T := hPH.2
  have hPB : 1 ≤ B P := by
    have h1 : ⌊B P⌋ ≠ 0 := hPH.1
    have h2 : 0 ≤ ⌊B P⌋ := Int.floor_nonneg.mpr (hB0 P)
    have h3 : 1 ≤ ⌊B P⌋ := by omega
    exact Int.le_floor.mp (by exact_mod_cast h3)
  have hdP : MMP.Flips.genericFiberPointDegree g P = 2 := by
    simp only [MMP.Flips.genericFiberPointDegree]
    rwa [if_pos hPh]
  obtain ⟨hgfd, -⟩ := exists_open_good_fibre sV sT hdimV hQ K hK B hlc ε hε g hg hdimT hnum
    P hPB hdP
  -- the horizontal part of `B` is `P`
  have hBh : ∀ Γ : Mori.PrimeDivisor V, g Γ.genericPoint = genericPoint T →
      B Γ = if Γ = P then 1 else 0 := by
    intro Γ hΓ
    unfold MMP.Flips.genericFiberDegree at hgfd
    have hterm : ∀ E ∈ B.support, 0 ≤ B.coeff E * MMP.Flips.genericFiberPointDegree g E :=
      fun E _ => mul_nonneg (hB0 E) (by positivity)
    have hPs : P ∈ B.support := by
      rw [Finsupp.mem_support_iff]; intro h; change B P = 0 at h; linarith
    have hPterm : B.coeff P * MMP.Flips.genericFiberPointDegree g P = 2 * B P := by
      rw [hdP]; change B P * ((2 : ℕ) : ℚ) = _; push_cast; ring
    by_cases hΓP : Γ = P
    · subst hΓP
      rw [if_pos rfl]
      have := Finset.single_le_sum hterm hPs
      rw [hPterm, hgfd] at this
      linarith
    · rw [if_neg hΓP]
      by_contra hne
      have hΓs : Γ ∈ B.support := Finsupp.mem_support_iff.mpr hne
      have hpos : 0 < B Γ := lt_of_le_of_ne (hB0 Γ) (Ne.symm hne)
      have h1 := one_le_genericFiberPointDegree sV sT hdimV hQ g hg hdimT Γ hΓ
      have h2 := Finset.sum_le_sum_of_subset_of_nonneg
        (show ({P, Γ} : Finset (Mori.PrimeDivisor V)) ⊆ B.support by
          intro E hE
          rcases Finset.mem_insert.mp hE with rfl | h
          · exact hPs
          · rw [Finset.mem_singleton] at h; subst h; exact hΓs)
        (fun E _ _ => hterm E ‹_›)
      rw [Finset.sum_pair (Ne.symm hΓP), hPterm, hgfd] at h2
      have h3 : (1 : ℚ) ≤ MMP.Flips.genericFiberPointDegree g Γ := by exact_mod_cast h1
      have h4 : 0 < B.coeff Γ * MMP.Flips.genericFiberPointDegree g Γ := by
        change 0 < B Γ * _; positivity
      linarith
  -- the normalization
  obtain ⟨hfin, hrange, hI, hres⟩ := hn
  have := hfin
  have hη := map_genericPoint_eq_of_range_eq ν P hrange
  have hsurjν := stalkMap_surjective_of_isIso_residueFieldMap hres
  have hφs : (ν ≫ g) ≫ sT = ν ≫ sV := by rw [Category.assoc, hgc.comp_eq]
  obtain ⟨hdimN, hcl0, hfibN⟩ := normalization_facts sV sT hdimV hdimT g hgc.comp_eq ν P hrange
  have : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace (ν ≫ sV)
  have hNv : IsNormalVariety k (ν ≫ sV) := ⟨⟨⟩, inferInstance⟩
  have hgη : g (ν (genericPoint N)) = genericPoint T := by rw [hη, hPh]
  let := functionFieldAlgebra sV
  let := functionFieldAlgebra sT
  let := functionFieldAlgebra (ν ≫ sV)
  -- a function on `T` with nonzero differential and a uniformizer along `P`
  obtain ⟨s, hs⟩ := exists_D_ne_zero (sT := sT) (d := 0) (by rw [hdimT]; rfl)
  have hsN := D_functionFieldMap_ne_zero sT (ν ≫ sV) (ν ≫ g) hφs hs
  obtain ⟨xs, hxs1, hxs2⟩ := exists_stalk_eq_functionFieldMap g ν hgη s
  obtain ⟨p₀, -, hp₀1⟩ := exists_ord_eq_one (T := V) (y := ν (genericPoint N))
    (by rw [hη]; exact P.coheight_genericPoint)
  set ϖt := algebraMap (V.presheaf.stalk (ν (genericPoint N))) V.functionField p₀ with hϖtdef
  have hϖt0 : ϖt ≠ 0 := by intro h; rw [h] at hp₀1; simp at hp₀1
  have hϖtP : V.ord ϖt P.genericPoint = 1 := by rw [← hη]; exact hp₀1
  -- the logarithmic 2-form `ωb = ϖ⁻¹ dϖ ∧ g^* ds` and its order along `P`
  set ωb : ⋀[V.functionField]^2 Ω[V.functionField⁄k] :=
    (algebraMap k V.functionField 1 * ϖt⁻¹) • exteriorPower.ιMulti V.functionField 2
      (Fin.cons (KaehlerDifferential.D k V.functionField ϖt) fun _ : Fin 1 =>
        KaehlerDifferential.D k V.functionField (functionFieldMap g s)) with hωbdef
  obtain ⟨e, he⟩ := letI := stalkAlgebra sV (ν (genericPoint N))
    exists_residueField_algEquiv (k := k) (ν.stalkMap (genericPoint N)).hom
      (fun c => stalkMap_algebraMap sV ν (genericPoint N) c) hsurjν
  have hxspan : letI := stalkAlgebra sV (ν (genericPoint N))
      Submodule.span (IsLocalRing.ResidueField (V.presheaf.stalk (ν (genericPoint N))))
        {KaehlerDifferential.D k (IsLocalRing.ResidueField
          (V.presheaf.stalk (ν (genericPoint N)))) (IsLocalRing.residue _ xs)} = ⊤ := by
    letI := stalkAlgebra sV (ν (genericPoint N))
    refine span_D_eq_top_of_algEquiv k e fun l => ?_
    rw [he, hxs2]
    exact exists_D_eq_smul_of_ne_zero (ν ≫ sV) hdimN hsN l
  obtain ⟨τb, hτb⟩ : ∃ τ : RationalPluriForms sV 2 ((1 : ℕ) : ℤ), τ = formPow ωb 1 := ⟨_, rfl⟩
  have hωbP : P.ordForm τb = -1 := by
    refine ordForm_dlog_frame_eq_neg_one (k₀ := k) (j := ν) P hη hdimV hp₀1 hxspan τb ?_
    rw [hτb, hωbdef, map_one, one_mul, hxs1]
  have hωb0 : ωb ≠ 0 := by
    intro h0
    have hτ0 : τb = 0 := by
      rw [hτb, h0]; exact (PiTensorProduct.tprod V.functionField).map_coord_zero (0 : Fin 1) rfl
    rw [hτ0, Mori.PrimeDivisor.ordForm_zero] at hωbP
    norm_num at hωbP
  -- the adjoint form `Ω₀` and the vertical divisor `E = div Ω₀ + m₁ B`
  obtain ⟨m₁, hm₁, Ω₀, MT, hMT, hMTf, hΩ₀0, hΩ₀⟩ :=
    exists_rationalPluriForm_ordForm_add_eq_pullback sV sT hdimV hQ K hK B hlc ε hε hklt g hg
      hdimT hnum
  have hΩ₀h : ∀ Γ : Mori.PrimeDivisor V, g Γ.genericPoint = genericPoint T →
      (Γ.ordForm Ω₀ : ℚ) = -(m₁ : ℚ) * B Γ := fun Γ hΓ => by
    have := hΩ₀ Γ
    rw [coeff_pullback_eq_zero_of_horizontal g hMT hMTf Γ hΓ, mul_zero] at this
    linarith
  have hEfin : (Function.support fun Γ : Mori.PrimeDivisor V =>
      (Γ.ordForm Ω₀ : ℚ) + m₁ * B Γ).Finite := by
    refine ((finite_ordForm_ne_zero Ω₀).union B.support.finite_toSet).subset fun Γ hΓ => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, Finsupp.mem_support_iff,
      not_or, not_not] at h
    apply hΓ
    simp [h.1, h.2]
  set E : QDivisor V := Finsupp.ofSupportFinite _ hEfin
  have hE : ∀ Γ, E Γ = (Γ.ordForm Ω₀ : ℚ) + m₁ * B Γ := fun Γ => rfl
  obtain ⟨m₀, hm₀, hm₀e, ψ, hψ0, hψfin, W, hW, hgenE, hWord, hWψ⟩ :=
    exists_localGenerator_of_vertical g hdimT hcl hirr E (fun Γ hΓ => by
      rw [hE, hΩ₀h Γ hΓ]; ring)
  -- `Ω₀ = c₀ ωb^{⊗m₁}` and `Ω* = c₀^{m₀} ωb^{⊗m₀ m₁}`
  obtain ⟨bV⟩ := exists_basis_topForms (sX := sV) (d := 2) (by rw [hdimV]; norm_cast)
  obtain ⟨Ωb, hΩb⟩ : ∃ Ω : RationalPluriForms sV 2 m₁, Ω = formPow ωb m₁ := ⟨_, rfl⟩
  have hΩb0 : Ωb ≠ 0 := hΩb ▸ formPow_ne_zero_of_ne_zero hdimV hωb0 m₁
  set c₀ := (ZTensorPower.basis bV m₁).repr Ω₀ () / (ZTensorPower.basis bV m₁).repr Ωb ()
    with hc₀def
  have hΩ₀c : Ω₀ = c₀ • formPow ωb m₁ := by
    rw [← hΩb]; exact eq_div_repr_smul bV Ω₀ Ωb (MMP.Mori.repr_ne_zero_of_ne_zero bV hΩb0)
  have hc₀0 : c₀ ≠ 0 := by rintro h; apply hΩ₀0; rw [hΩ₀c, h]; exact zero_smul _ _
  set M := m₀ * m₁ with hMdef
  have hM : 0 < M := Nat.mul_pos hm₀ hm₁
  have hMe : Even M := hm₀e.mul_right m₁
  obtain ⟨Ωs, hΩs⟩ : ∃ Ω : RationalPluriForms sV 2 M, Ω = c₀ ^ m₀ • formPow ωb M := ⟨_, rfl⟩
  have hΩs0 : Ωs ≠ 0 := hΩs ▸ smul_ne_zero (pow_ne_zero _ hc₀0)
    (formPow_ne_zero_of_ne_zero hdimV hωb0 M)
  have hpow : ∀ c : V.functionField, c ≠ 0 → ∀ (n : ℕ) (Γ : Mori.PrimeDivisor V),
      V.ord (c ^ n) Γ.genericPoint = n * V.ord c Γ.genericPoint := fun c hc n Γ => by
    rw [show c ^ n = c ^ (n : ℤ) from (zpow_natCast _ _).symm, MMP.Mori.ord_zpow _ hc]
  have hordΩs : ∀ Γ : Mori.PrimeDivisor V, (Γ.ordForm Ωs : ℚ) = m₀ * Γ.ordForm Ω₀ := by
    intro Γ
    have e1 := ordForm_smul_formPow hdimV Γ hωb0 (pow_ne_zero _ hc₀0) M Ωs hΩs τb hτb
    have e2 := ordForm_smul_formPow hdimV Γ hωb0 hc₀0 m₁ Ω₀ hΩ₀c τb hτb
    rw [e1, e2, hpow c₀ hc₀0 m₀ Γ, hMdef]
    push_cast; ring
  have hgen : ∀ t (Γ : Mori.PrimeDivisor V), (Γ.support ∩ g ⁻¹ᵁ W t).Nonempty →
      (V.ord (functionFieldMap g (ψ t)) Γ.genericPoint : ℚ) + Γ.ordForm Ωs + M * B Γ = 0 := by
    intro t Γ h
    have := hgenE t Γ h
    rw [hE] at this
    rw [hordΩs, hMdef]
    push_cast
    linear_combination this
  have hΩsh : ∀ Γ : Mori.PrimeDivisor V, g Γ.genericPoint = genericPoint T →
      Γ.ordForm Ωs = -(M : ℤ) * (if Γ = P then 1 else 0) := by
    intro Γ hΓ
    have h1 := hordΩs Γ
    rw [hΩ₀h Γ hΓ, hBh Γ hΓ] at h1
    have h2 : (Γ.ordForm Ωs : ℚ) = ((-(M : ℤ) * (if Γ = P then 1 else 0) : ℤ) : ℚ) := by
      rw [h1, hMdef]; split_ifs <;> push_cast <;> ring
    exact_mod_cast h2
  -- the residue `ρ*` of `Ω*`
  have hcP : V.ord (c₀ ^ m₀) (ν (genericPoint N)) = 0 := by
    have e1 := ordForm_smul_formPow hdimV P hωb0 (pow_ne_zero _ hc₀0) M Ωs hΩs τb hτb
    rw [hΩsh P hPh, if_pos rfl, hωbP] at e1
    rw [hη]
    linarith
  obtain ⟨cu, hcu, hcue⟩ := exists_isUnit_algebraMap_eq_of_ord_eq_zero
    (by rw [hη]; exact P.coheight_genericPoint) (pow_ne_zero _ hc₀0) hcP
  obtain ⟨ρs, hρs⟩ : ∃ ρ : RationalPluriForms (ν ≫ sV) 1 M, ρ =
      (ν.stalkMap (genericPoint N)).hom cu • formPow (exteriorPower.ιMulti N.functionField 1
        fun _ : Fin 1 => KaehlerDifferential.D k N.functionField (functionFieldMap (ν ≫ g) s)) M :=
    ⟨_, rfl⟩
  have hρs0 : ρs ≠ 0 := hρs ▸ smul_ne_zero ((hcu.map _).ne_zero)
    (formPow_ne_zero_of_ne_zero (sX := ν ≫ sV) hdimN (ιMulti_fin_one_ne_zero hsN) M)
  have hresΩ : ∀ a : T.functionField, IsPoincareResidue sV ν 1 M (functionFieldMap g a • Ωs)
      (functionFieldMap (ν ≫ g) a • ρs) := by
    intro a
    obtain ⟨ca, hca1, hca2⟩ := exists_stalk_eq_functionFieldMap g ν hgη a
    have h := isPoincareResidue_smul_formPow_dlog_of_surjective (sY := sV) (j := ν) P hη hsurjν
      hdimV 1 hϖt0 xs (ca * cu) (by rw [hxs2]; exact hsN) M
    have e1 : (algebraMap _ V.functionField (ca * cu) • formPow ((algebraMap k V.functionField 1 *
        ϖt⁻¹) • exteriorPower.ιMulti V.functionField 2 (Fin.cons (KaehlerDifferential.D k
          V.functionField ϖt) fun _ : Fin 1 => KaehlerDifferential.D k V.functionField
            (algebraMap _ V.functionField xs))) M : RationalPluriForms sV 2 M) =
        functionFieldMap g a • Ωs := by
      rw [hΩs, map_mul, hca1, hcue, hxs1]
      exact mul_smul _ _ _
    have e2 : (((ν.stalkMap (genericPoint N)).hom (ca * cu) * (algebraMap k N.functionField 1 *
        (V.ord ϖt (ν (genericPoint N)) : N.functionField)) ^ M) •
          formPow (exteriorPower.ιMulti N.functionField 1 fun _ : Fin 1 =>
            KaehlerDifferential.D k N.functionField ((ν.stalkMap (genericPoint N)).hom xs)) M :
        RationalPluriForms (ν ≫ sV) 1 M) = functionFieldMap (ν ≫ g) a • ρs := by
      rw [hρs, map_mul, hca2, hxs2, hp₀1, map_one, Int.cast_one, one_mul, one_pow, mul_one]
      exact mul_smul _ _ _
    rw [e1, e2] at h
    exact h
  obtain ⟨Θ, hΘadj, hΘ⟩ := exists_adjunctionBoundary_of_residue sV hdimV hdimT g B N ν hdimN hfibN
    hcl0 hM Ωs hΩs0 ψ hψ0 hψfin W hW hgen hWord hWψ ρs hρs0 hresΩ
  have hres1 : IsPoincareResidue sV ν 1 M Ωs ρs := by
    have := hresΩ 1; rwa [map_one, one_smul, map_one, one_smul] at this
  -- the residue `ρ*` is fixed by every automorphism over `k(T)`
  have hinv : ∀ τ : FunctionFieldEquiv (ν ≫ sV) (ν ≫ sV),
      (∀ a, τ (functionFieldMap (ν ≫ g) a) = functionFieldMap (ν ≫ g) a) →
      pluriformPullback (ν ≫ sV) (ν ≫ sV) (FunctionFieldEquiv.toHom (ν ≫ sV) (ν ≫ sV) τ) 1 M ρs =
        ρs := fun τ hτ =>
    pluriformPullback_eq_of_bisection sV sT hdimV hQ K hK B hlc ε hε hklt g hg hdimT hnum P hPh
      hPB hdP N ν hrange hres hM hMe Ωs hΩs0 hΩsh hres1 τ hτ
  refine ⟨Θ, hΘadj, 1, one_pos, fun σ hσ => ⟨?_, ?_⟩⟩
  · -- crepancy
    have hpair : MMP.Mori.IsPair (ν ≫ sV) Θ := by
      obtain ⟨KN, hKN⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (ν ≫ sV) hNv
        (n := 1) (by rw [hdimN]; rfl)
      exact MMP.Mori.isPair_of_isCanonicalDivisor hNv hKN
        (isQCartier_of_isQFactorial (ν ≫ sV) (isQFactorial_of_isClosed_genericPoint hNv fun Q =>
          isClosed_singleton_of_ne_genericPoint (ν ≫ sV) hdimN
            (PrimeDivisor.genericPoint_ne_genericPoint Q)) _)
    have hcomp : ∀ τ : FunctionFieldEquiv (ν ≫ sV) (ν ≫ sV),
        (∀ a, τ (functionFieldMap (ν ≫ g) a) = functionFieldMap (ν ≫ g) a) →
        ∀ Q : Mori.PrimeDivisor N, ∃ Q' : Mori.PrimeDivisor N, (∀ a : N.functionField, a ≠ 0 →
          N.ord (τ a) Q.genericPoint = N.ord a Q'.genericPoint) ∧ Θ.coeff Q' = Θ.coeff Q := by
      intro τ hτ Q
      obtain ⟨Q', hQ'φ, hQ'⟩ := exists_primeDivisor_ord_comp_eq hdimN (ν ≫ g) τ hτ Q (hcl0 Q)
      refine ⟨Q', hQ', ?_⟩
      rw [show Θ.coeff Q' = Θ Q' from rfl, show Θ.coeff Q = Θ Q from rfl, hΘ Q', hΘ Q, hQ'φ]
      have h1 := ordForm_pluriformPullback_eq hdimN hNv τ Q Q' hQ' ρs hρs0
      rw [hinv τ hτ] at h1
      have h2 := hQ' (functionFieldMap (ν ≫ g) (ψ ((ν ≫ g) Q.genericPoint)))
        ((map_ne_zero _).mpr (hψ0 _))
      rw [hτ] at h2
      rw [← h1, ← h2]
    have hσ' : ∀ a, σ.symm (functionFieldMap (ν ≫ g) a) = functionFieldMap (ν ≫ g) a := by
      intro a
      apply σ.injective
      rw [AlgEquiv.apply_symm_apply, hσ a]
    exact isCrepantBirationalMap_of_ord_comp_eq hNv hdimN hpair σ (hcomp σ hσ) (hcomp σ.symm hσ')
  · -- residues of vertical adjoint forms
    intro m _ hme Ω hΩ ρ hρ
    obtain ⟨U, hηU, φ, hU⟩ := hΩ (genericPoint T)
    have hΩ0 : Ω ≠ 0 := fun h => hU.1 (by rw [h, smul_zero])
    have hφ0 : φ ≠ 0 := fun h => hU.1 (by rw [h, map_zero, zero_smul])
    have hd2 : topologicalKrullDim V = ((2 : ℕ) : WithBot ℕ∞) := by rw [hdimV]; rfl
    have hΩh : ∀ Γ : Mori.PrimeDivisor V, g Γ.genericPoint = genericPoint T →
        Γ.ordForm Ω = -(m : ℤ) * (if Γ = P then 1 else 0) := by
      intro Γ hΓ
      have hmeet : (Γ.support ∩ g ⁻¹ᵁ U).Nonempty := by
        refine ⟨Γ.genericPoint, ?_, ?_⟩
        · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
        · change g Γ.genericPoint ∈ U; rw [hΓ]; exact hηU
      have e1 := hU.2 Γ hmeet
      rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hd2 ((map_ne_zero _).mpr hφ0) hΩ0,
        ord_functionFieldMap_eq_zero g Γ hΓ hφ0, zero_add, show B.coeff Γ = B Γ from rfl,
        hBh Γ hΓ] at e1
      have h2 : (Γ.ordForm Ω : ℚ) = ((-(m : ℤ) * (if Γ = P then 1 else 0) : ℤ) : ℚ) := by
        split_ifs at e1 ⊢ <;> push_cast at e1 ⊢ <;> linarith
      exact_mod_cast h2
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · -- weight zero: `Ω` is a function pulled back from `T`
      subst hm0
      obtain ⟨Ωz, hΩz⟩ : ∃ Ω' : RationalPluriForms sV 2 ((0 : ℕ) : ℤ), Ω' = formPow ωb 0 :=
        ⟨_, rfl⟩
      have hΩz0 : Ωz ≠ 0 := hΩz ▸ formPow_ne_zero_of_ne_zero hdimV hωb0 0
      set cz := (ZTensorPower.basis bV ((0 : ℕ) : ℤ)).repr Ω () /
        (ZTensorPower.basis bV ((0 : ℕ) : ℤ)).repr Ωz () with hczdef
      have hΩc : Ω = cz • formPow ωb 0 := by
        rw [← hΩz]; exact eq_div_repr_smul bV Ω Ωz (MMP.Mori.repr_ne_zero_of_ne_zero bV hΩz0)
      have hcz0 : cz ≠ 0 := by rintro h; apply hΩ0; rw [hΩc, h]; exact zero_smul _ _
      have hczh : ∀ Γ : Mori.PrimeDivisor V, g Γ.genericPoint = genericPoint T →
          V.ord cz Γ.genericPoint = 0 := by
        intro Γ hΓ
        have e1 := ordForm_smul_formPow hdimV Γ hωb0 hcz0 0 Ω hΩc τb hτb
        rw [hΩh Γ hΓ] at e1
        simpa using e1.symm
      obtain ⟨a, ha⟩ := exists_functionFieldMap_eq_of_forall_ord_eq_zero g hgc.isIso_app hcl hcz0
        hczh
      obtain ⟨ca, hca1, hca2⟩ := exists_stalk_eq_functionFieldMap g ν hgη a
      letI := stalkAlgebra sV (ν (genericPoint N))
      have hpres : Ω = (algebraMap _ V.functionField ca • formPow ((algebraMap _ V.functionField
          p₀)⁻¹ • exteriorPower.ιMulti V.functionField 2 (Fin.cons (KaehlerDifferential.D k
            V.functionField (algebraMap _ _ p₀)) fun _ : Fin 1 => KaehlerDifferential.D k
              V.functionField (algebraMap _ _ xs))) 0 : RationalPluriForms sV 2 ((0 : ℕ) : ℤ)) := by
        rw [hΩc, hca1, ha]
        congr 1
        simp only [formPow]
        congr 1
        funext i
        exact i.elim0
      have hres' := residue_eq_of_presentation ν P hη hsurjν (specializes_refl _)
        hϖtP Ω hpres hρ
      have hid : ∀ z, (V.presheaf.stalkSpecializes
          (specializes_refl (ν (genericPoint N)))).hom z = z := fun z => by
        rw [TopCat.Presheaf.stalkSpecializes_refl]; rfl
      rw [hid, hid, hca2, hxs2] at hres'
      rw [hres', pluriformPullback_smul_formPow_D (ν ≫ sV) (ν ≫ sV) hdimN hdimN _
        (functionFieldMap (ν ≫ g) s) (functionFieldMap (ν ≫ g) a) hsN 0]
      rw [show FunctionFieldEquiv.toHom (ν ≫ sV) (ν ≫ sV) σ (functionFieldMap (ν ≫ g) a) =
          functionFieldMap (ν ≫ g) a from hσ a,
        show FunctionFieldEquiv.toHom (ν ≫ sV) (ν ≫ sV) σ (functionFieldMap (ν ≫ g) s) =
          functionFieldMap (ν ≫ g) s from hσ s]
    · exact pluriformPullback_eq_of_bisection sV sT hdimV hQ K hK B hlc ε hε hklt g hg hdimT hnum
        P hPh hPB hdP N ν hrange hres hm0 hme Ω hΩ0 hΩh hρ σ hσ

/-- **Two sections.** Their identification is crepant and matches the residues of vertical
adjoint pluriforms. -/
private theorem twoSections_clause
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T]
    (hdimV : topologicalKrullDim V = 2) (hQ : IsQFactorial sV)
    (K : Divisor V) (hK : K.IsCanonicalDivisor sV 2)
    (B : QDivisor V) (hlc : MMP.Intersection.IsLogCanonicalPair sV B)
    (ε : ℚ) (hε : 0 < ε ∧ ε < 1)
    (hklt : IsKltPair sV (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))
    (g : V ⟶ T) [IsDominant g]
    (hg : IsMoriFibreSpace sV sT K (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)) g)
    (hdimT : topologicalKrullDim T = 1)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sV g
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)))
    (P₁ P₂ : Mori.PrimeDivisor V) (hne : P₁ ≠ P₂) (hH : {P' : Mori.PrimeDivisor V | ⌊B.coeff P'⌋ ≠ 0 ∧ g.base P'.genericPoint = genericPoint T} = {P₁, P₂})
    (hd₁ : (letI := (g.residueFieldMap P₁.genericPoint).hom.toAlgebra
      Module.finrank (T.residueField (g.base P₁.genericPoint)) (V.residueField P₁.genericPoint)) = 1)
    (hd₂ : (letI := (g.residueFieldMap P₂.genericPoint).hom.toAlgebra
      Module.finrank (T.residueField (g.base P₂.genericPoint)) (V.residueField P₂.genericPoint)) = 1) :
    let IsNormalization : ∀ (P : Mori.PrimeDivisor V) (N : Scheme.{0}), (N ⟶ V) → Prop :=
      fun P N ν => IsFinite ν ∧ Set.range ν.base = (P.support : Set V) ∧
        ∃ _ : IsIntegral N, IsIso (ν.residueFieldMap (genericPoint N))
    let IsAdjunctionBoundary :
        ∀ (N : Scheme.{0}) [IsIntegral N] [IsLocallyNoetherian N] (ν : N ⟶ V), QDivisor N → Prop :=
      fun N _ _ ν Θ => ∃ m : ℕ, 0 < m ∧ ∀ x : N, ∃ U : V.Opens, ν.base x ∈ U ∧
        ∃ τ : RationalPluriForms sV 2 m, GeneratesOn B m U τ ∧
          ∃ ρ : RationalPluriForms (ν ≫ sV) 1 m, IsPoincareResidue sV ν 1 m τ ρ ∧
            GeneratesOn Θ m (ν ⁻¹ᵁ U) ρ
    let IsVerticalAdjoint : ∀ m : ℕ, RationalPluriForms sV 2 m → Prop :=
      fun m Ω => ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ φ : T.functionField,
        GeneratesOn B m (g ⁻¹ᵁ U) (functionFieldMap g φ • Ω)
      ∀ (N₁ : Scheme.{0}) [IsIntegral N₁] [IsLocallyNoetherian N₁] [IsNormal N₁] (ν₁ : N₁ ⟶ V)
        [IsDominant (ν₁ ≫ g)] (N₂ : Scheme.{0}) [IsIntegral N₂] [IsLocallyNoetherian N₂]
        [IsNormal N₂] (ν₂ : N₂ ⟶ V) [IsDominant (ν₂ ≫ g)],
        IsNormalization P₁ N₁ ν₁ → IsNormalization P₂ N₂ ν₂ →
        ∃ Θ₁ : QDivisor N₁, IsAdjunctionBoundary N₁ ν₁ Θ₁ ∧
        ∃ Θ₂ : QDivisor N₂, IsAdjunctionBoundary N₂ ν₂ Θ₂ ∧ ∃ m₀ : ℕ, 0 < m₀ ∧
          ∀ σ : FunctionFieldEquiv (ν₁ ≫ sV) (ν₂ ≫ sV),
            (∀ a, σ (functionFieldMap (ν₂ ≫ g) a) = functionFieldMap (ν₁ ≫ g) a) →
            IsCrepantBirationalMap (ν₁ ≫ sV) (ν₂ ≫ sV) Θ₁ Θ₂ σ ∧
            ∀ m : ℕ, m₀ ∣ m → Even m → ∀ Ω : RationalPluriForms sV 2 m, IsVerticalAdjoint m Ω →
              ∀ (ρ₁ : RationalPluriForms (ν₁ ≫ sV) 1 m) (ρ₂ : RationalPluriForms (ν₂ ≫ sV) 1 m),
                IsPoincareResidue sV ν₁ 1 m Ω ρ₁ → IsPoincareResidue sV ν₂ 1 m Ω ρ₂ →
                pluriformPullback (ν₁ ≫ sV) (ν₂ ≫ sV)
                  (FunctionFieldEquiv.toHom (ν₁ ≫ sV) (ν₂ ≫ sV) σ) 1 m ρ₂ = ρ₁ := by
  classical
  intro IsNormalization IsAdjunctionBoundary IsVerticalAdjoint N₁ _ _ _ ν₁ _ N₂ _ _ _ ν₂ _ hn₁ hn₂
  obtain ⟨hVv, hVproj⟩ := (Mori.isProjectiveVariety_iff k sV).mp hg.isProjectiveVariety
  have : IsProper sV := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hVproj).2
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have : IsSeparated sV := hVv.toIsSeparated
  have hgc := hg.isContraction
  obtain ⟨hTv, hTn⟩ := hgc.isNormalVariety_target
  have : IsNormal T := hTn
  have : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  have : IsSeparated sT := hTv.toIsSeparated
  have : QuasiCompact sT := hTv.toQuasiCompact
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsProper g :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hgc.isProjectiveMorphism).2
  have hirr := isIrreducible_fibre_of_isMoriFibreSpace sV sT hdimV hQ hg hdimT
  have hcl : ∀ y : T, y ≠ genericPoint T → IsClosed ({y} : Set T) := fun y hy =>
    isClosed_singleton_of_ne_genericPoint sT hdimT hy
  have hB0 : ∀ E, 0 ≤ B E := hlc.2.1
  have hP₁H : P₁ ∈ {P' : Mori.PrimeDivisor V |
      ⌊B.coeff P'⌋ ≠ 0 ∧ g.base P'.genericPoint = genericPoint T} := by
    rw [hH]; exact Or.inl rfl
  have hP₂H : P₂ ∈ {P' : Mori.PrimeDivisor V |
      ⌊B.coeff P'⌋ ≠ 0 ∧ g.base P'.genericPoint = genericPoint T} := by
    rw [hH]; exact Or.inr rfl
  have hP₁h : g P₁.genericPoint = genericPoint T := hP₁H.2
  have hP₂h : g P₂.genericPoint = genericPoint T := hP₂H.2
  have hBge : ∀ P ∈ {P' : Mori.PrimeDivisor V |
      ⌊B.coeff P'⌋ ≠ 0 ∧ g.base P'.genericPoint = genericPoint T}, 1 ≤ B P := fun P hP => by
    have h1 : ⌊B P⌋ ≠ 0 := hP.1
    have h2 : 0 ≤ ⌊B P⌋ := Int.floor_nonneg.mpr (hB0 P)
    have h3 : 1 ≤ ⌊B P⌋ := by omega
    exact Int.le_floor.mp (by exact_mod_cast h3)
  -- the normalizations are sections
  obtain ⟨hfin₁, hrange₁, hI₁, hres₁⟩ := hn₁
  obtain ⟨hfin₂, hrange₂, hI₂, hres₂⟩ := hn₂
  have := hfin₁
  have := hfin₂
  have hiso₁ : IsIso (ν₁ ≫ g) := isIso_comp_of_finrank_eq_one sV sT hTv hVv hdimV hdimT g
    hgc.comp_eq P₁ hP₁h hd₁ ν₁ hrange₁ hres₁
  have hiso₂ : IsIso (ν₂ ≫ g) := isIso_comp_of_finrank_eq_one sV sT hTv hVv hdimV hdimT g
    hgc.comp_eq P₂ hP₂h hd₂ ν₂ hrange₂ hres₂
  have : IsClosedImmersion ν₁ := IsClosedImmersion.of_comp ν₁ g
  have : IsClosedImmersion ν₂ := IsClosedImmersion.of_comp ν₂ g
  have hη₁ := map_genericPoint_eq_of_range_eq ν₁ P₁ hrange₁
  have hη₂ := map_genericPoint_eq_of_range_eq ν₂ P₂ hrange₂
  have : CompactSpace N₁ := QuasiCompact.compactSpace_of_compactSpace (ν₁ ≫ sV)
  have : CompactSpace N₂ := QuasiCompact.compactSpace_of_compactSpace (ν₂ ≫ sV)
  have hdimN₁ : topologicalKrullDim N₁ = 1 := by
    rw [← hdimT]
    exact (Scheme.homeoOfIso (asIso (ν₁ ≫ g))).isHomeomorph.topologicalKrullDim_eq
  have hdimN₂ : topologicalKrullDim N₂ = 1 := by
    rw [← hdimT]
    exact (Scheme.homeoOfIso (asIso (ν₂ ≫ g))).isHomeomorph.topologicalKrullDim_eq
  -- a rational function with horizontal divisor `n (P₁ - P₂)`
  obtain ⟨M', hM', hMf', n, hn, φz, hφz⟩ := exists_qLinearlyEquivalent_sub_single sV sT hdimV hQ
    K hK B hlc ε hε hklt g hg hdimT hnum P₁ P₂ hP₁h hP₂h hd₁ hd₂
  obtain ⟨f, hf0, hford⟩ := MMP.Positivity.exists_ord_eq_of_units φz
  have hsing : ∀ (P Γ : Mori.PrimeDivisor V),
      (Divisor.toQDivisor (Finsupp.single P 1)) Γ = if Γ = P then 1 else 0 := fun P Γ => by
    change DivisorWithCoeffs.coeff (Divisor.toQDivisor (Finsupp.single P 1)) Γ = _
    rw [Divisor.coeff_toQDivisor]
    by_cases h : Γ = P
    · subst h; rw [DivisorWithCoeffs.coeff_single_self, if_pos rfl]; simp
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm h), if_neg h]; simp
  have hordh : ∀ Γ : Mori.PrimeDivisor V, g Γ.genericPoint = genericPoint T →
      (V.ord f Γ.genericPoint : ℚ) =
        n * ((if Γ = P₁ then 1 else 0) - (if Γ = P₂ then 1 else 0)) := by
    intro Γ hΓ
    have h1 := congrArg (fun D : QDivisor V => D Γ) hφz
    simp only [Finsupp.smul_apply, Finsupp.sub_apply, zsmul_eq_mul] at h1
    have h2 : (Divisor.toQDivisor (principalDivisor φz)) Γ = (Γ.ord φz : ℚ) := by
      change DivisorWithCoeffs.coeff (Divisor.toQDivisor (principalDivisor φz)) Γ = _
      rw [Divisor.coeff_toQDivisor, coeff_principalDivisor]
    rw [h2, hsing, hsing, coeff_pullback_eq_zero_of_horizontal g hM' hMf' Γ hΓ] at h1
    rw [← hford Γ, ← h1]
    push_cast; ring
  have hf₁ : V.ord f P₁.genericPoint = 1 * n := by
    have h := hordh P₁ hP₁h
    rw [if_pos rfl, if_neg hne] at h
    have : ((V.ord f P₁.genericPoint : ℤ) : ℚ) = ((1 * n : ℤ) : ℚ) := by rw [h]; push_cast; ring
    exact_mod_cast this
  have hf₂ : V.ord f P₂.genericPoint = -1 * n := by
    have h := hordh P₂ hP₂h
    rw [if_neg (Ne.symm hne), if_pos rfl] at h
    have : ((V.ord f P₂.genericPoint : ℤ) : ℚ) = ((-1 * n : ℤ) : ℚ) := by
      rw [h]; push_cast; ring
    exact_mod_cast this
  have hf0' : ∀ Γ : Mori.PrimeDivisor V, g Γ.genericPoint = genericPoint T → Γ ≠ P₁ →
      Γ ≠ P₂ → V.ord f Γ.genericPoint = 0 := by
    intro Γ hΓ h1 h2
    have h := hordh Γ hΓ
    rw [if_neg h1, if_neg h2] at h
    have : ((V.ord f Γ.genericPoint : ℤ) : ℚ) = 0 := by rw [h]; ring
    exact_mod_cast this
  -- a rational function on `T` with nonzero differential
  obtain ⟨s, hs⟩ := exists_D_ne_zero (sT := sT) (d := 0) (by rw [hdimT]; rfl)
  have hsN : ∀ (N : Scheme.{0}) [IsIntegral N] (ν : N ⟶ V) [IsDominant (ν ≫ g)],
      IsIso (ν ≫ g) → letI := functionFieldAlgebra (ν ≫ sV)
      KaehlerDifferential.D k N.functionField (functionFieldMap (ν ≫ g) s) ≠ 0 := by
    intro N _ ν _ hiso
    let := functionFieldAlgebra sT
    let := functionFieldAlgebra (ν ≫ sV)
    have hb : Function.Bijective (functionFieldMap (ν ≫ g)) :=
      MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion (ν ≫ g) ⊤ (by simp)
    have hh : (ν ≫ g) ≫ sT = ν ≫ sV := by rw [Category.assoc, hgc.comp_eq]
    have hb' : Function.Bijective (functionFieldHomOfEq (ν ≫ sV) sT (ν ≫ g) hh) := by
      convert hb using 1
      funext a
      exact functionFieldHomOfEq_apply _ _ _ hh a
    have := D_ne_zero_of_algEquiv (AlgEquiv.ofBijective _ hb') hs
    rwa [AlgEquiv.ofBijective_apply, functionFieldHomOfEq_apply] at this
  have hs₁ := hsN N₁ ν₁ hiso₁
  have hs₂ := hsN N₂ ν₂ hiso₂
  -- the logarithmic 2-form `ω₀ = n⁻¹ df/f ∧ g^* ds`
  let := functionFieldAlgebra sV
  set ω₀ : ⋀[V.functionField]^2 Ω[V.functionField⁄k] :=
    (algebraMap k V.functionField (n : k)⁻¹ * f⁻¹) • exteriorPower.ιMulti V.functionField 2
      (Fin.cons (KaehlerDifferential.D k V.functionField f) fun _ : Fin 1 =>
        KaehlerDifferential.D k V.functionField (functionFieldMap g s)) with hω₀def
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ₁ : RationalPluriForms sV 2 ((1 : ℕ) : ℤ), τ₁ = formPow ω₀ 1 :=
    ⟨_, rfl⟩
  have hn0k : (n : k) ≠ 0 := by exact_mod_cast hn.ne'
  have hω0 : ω₀ ≠ 0 := by
    intro h0
    let := functionFieldAlgebra (ν₁ ≫ sV)
    have hgη : g (ν₁ (genericPoint N₁)) = genericPoint T := by rw [hη₁, hP₁h]
    obtain ⟨c, hc1, hc2⟩ := exists_stalk_eq_functionFieldMap g ν₁ hgη 1
    obtain ⟨xs, hx1, hx2⟩ := exists_stalk_eq_functionFieldMap g ν₁ hgη s
    have h := isPoincareResidue_smul_formPow_dlog_of_surjective (sY := sV) (j := ν₁) P₁ hη₁
      (ν₁.stalkMap_surjective _) hdimV ((n : k)⁻¹)
      hf0 xs c (by rw [hx2]; exact hs₁) 1
    rw [hx1, ← hω₀def, h0] at h
    have hcoh : Order.coheight (ν₁ (genericPoint N₁)) = 1 := by
      rw [hη₁]; exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P₁
    obtain ⟨p, -, hp1⟩ := exists_ord_eq_one hcoh
    have h' : IsPoincareResidue sV ν₁ 1 1 (algebraMap _ V.functionField c •
        (formPow (0 : ⋀[V.functionField]^2 Ω[V.functionField⁄k]) 1 :
          RationalPluriForms sV 2 ((1 : ℕ) : ℤ))) 0 := by
      refine ⟨p, 0, fun _ => xs, hp1, ?_, ?_⟩
      · rw [map_zero, zero_smul,
          show (formPow (0 : ⋀[V.functionField]^2 Ω[V.functionField⁄k]) 1 :
            RationalPluriForms sV 2 ((1 : ℕ) : ℤ)) = 0 from
            (PiTensorProduct.tprod V.functionField).map_coord_zero (0 : Fin 1) rfl, smul_zero]
        <;> rfl
      · rw [map_zero, zero_smul]
        <;> rfl
    have e := IsPoincareResidue.unique_of_isClosedImmersion P₁ hη₁ h h'
    have hf₁' : V.ord f (ν₁ (genericPoint N₁)) = 1 * n := by rw [hη₁]; exact hf₁
    rw [hc2, map_one, one_mul, hf₁', pow_one] at e
    have hne0 : (algebraMap k N₁.functionField (n : k)⁻¹ * ((1 * n : ℤ) : N₁.functionField)) ≠ 0 := by
      rw [map_inv₀, map_natCast]
      have : CharZero N₁.functionField :=
        charZero_of_injective_algebraMap (algebraMap k N₁.functionField).injective
      have hn' : (n : N₁.functionField) ≠ 0 := by exact_mod_cast hn.ne'
      push_cast
      field_simp
      exact one_ne_zero
    rw [hx2] at e
    exact smul_ne_zero hne0 (formPow_ne_zero_of_ne_zero (sX := ν₁ ≫ sV) hdimN₁
      (ιMulti_fin_one_ne_zero hs₁) 1) e
  -- orders of `ω₀` along horizontal prime divisors
  have hτ₁0 : τ₁ ≠ 0 := by rw [hτ₁]; exact formPow_ne_zero_of_ne_zero hdimV hω0 1
  have hωge : ∀ Γ : Mori.PrimeDivisor V, g.base Γ.genericPoint = genericPoint T →
      0 ≤ ((Γ.ordForm τ₁ : ℤ) : ℚ) + B Γ := by
    intro Γ hΓ
    obtain ⟨xO, hxO⟩ := functionFieldMap_mem_range_of_horizontal g Γ hΓ s
    have h := ordForm_dlog_ge hdimV Γ hf0 xO ((n : k)⁻¹) τ₁ (by rw [hτ₁, hxO]) hτ₁0
    by_cases hΓP : Γ = P₁ ∨ Γ = P₂
    · have hB1 := hBge Γ (by rcases hΓP with rfl | rfl; exacts [hP₁H, hP₂H])
      have h1 : (-1 : ℤ) ≤ Γ.ordForm τ₁ := le_trans (by split_ifs <;> norm_num) h
      have h2 : (-1 : ℚ) ≤ Γ.ordForm τ₁ := by exact_mod_cast h1
      linarith
    · push Not at hΓP
      rw [if_pos (hf0' Γ hΓ hΓP.1 hΓP.2)] at h
      have h2 : (0 : ℚ) ≤ Γ.ordForm τ₁ := by exact_mod_cast h
      linarith [hB0 Γ]
  have hhor : ∀ Γ : Mori.PrimeDivisor V, g.base Γ.genericPoint = genericPoint T →
      ((Γ.ordForm τ₁ : ℤ) : ℚ) + B Γ = 0 := fun Γ hΓ => by
    have := ordForm_eq_neg_coeff_of_horizontal sV sT hdimV hQ K hK B hlc ε hε hklt g hg hdimT
      hnum hω0 τ₁ hτ₁ hωge Γ hΓ
    linarith
  -- local generators of the vertical part
  have hEfin : (Function.support fun Γ : Mori.PrimeDivisor V =>
      ((Γ.ordForm τ₁ : ℤ) : ℚ) + B Γ).Finite := by
    refine ((finite_ordForm_ne_zero τ₁).union B.support.finite_toSet).subset fun Γ hΓ => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, Finsupp.mem_support_iff,
      not_or, not_not] at h
    apply hΓ
    simp [h.1, h.2]
  set E : QDivisor V := Finsupp.ofSupportFinite _ hEfin
  have hE : ∀ Γ, E Γ = ((Γ.ordForm τ₁ : ℤ) : ℚ) + B Γ := fun Γ => rfl
  obtain ⟨m₀, hm₀, hm₀e, ψ, hψ0, hψfin, W, hW, hgenE, hWord, hWψ⟩ :=
    exists_localGenerator_of_vertical g hdimT hcl hirr E (fun Γ hΓ => by rw [hE]; exact hhor Γ hΓ)
  have hgen : ∀ t (Γ : Mori.PrimeDivisor V), (Γ.support ∩ g ⁻¹ᵁ W t).Nonempty →
      (V.ord (functionFieldMap g (ψ t)) Γ.genericPoint : ℚ) +
        m₀ * (((Γ.ordForm τ₁ : ℤ) : ℚ) + B Γ) = 0 := fun t Γ h => by
    rw [← hE]; exact hgenE t Γ h
  -- the two branches
  obtain ⟨τN₁, hτN₁⟩ : ∃ τ : RationalPluriForms (ν₁ ≫ sV) 1 ((1 : ℕ) : ℤ),
      (letI := functionFieldAlgebra (ν₁ ≫ sV)
      τ = formPow (exteriorPower.ιMulti N₁.functionField 1 fun _ : Fin 1 =>
        KaehlerDifferential.D k N₁.functionField (functionFieldMap (ν₁ ≫ g) s)) 1) := ⟨_, rfl⟩
  obtain ⟨τN₂, hτN₂⟩ : ∃ τ : RationalPluriForms (ν₂ ≫ sV) 1 ((1 : ℕ) : ℤ),
      (letI := functionFieldAlgebra (ν₂ ≫ sV)
      τ = formPow (exteriorPower.ιMulti N₂.functionField 1 fun _ : Fin 1 =>
        KaehlerDifferential.D k N₂.functionField (functionFieldMap (ν₂ ≫ g) s)) 1) := ⟨_, rfl⟩
  obtain ⟨Θ₁, hΘ₁adj, hΘ₁, hres₁'⟩ := exists_adjunctionBoundary_of_section sV sT hdimV hdimT g B
    hf0 hn s ω₀ rfl hω0 τ₁ hτ₁ m₀ hm₀ hm₀e ψ hψ0 hψfin W hW hgen hWord hWψ P₁ hP₁h N₁ ν₁ hη₁ 1
    (by rw [hf₁]) (by norm_num) hs₁ τN₁ hτN₁
  obtain ⟨Θ₂, hΘ₂adj, hΘ₂, hres₂'⟩ := exists_adjunctionBoundary_of_section sV sT hdimV hdimT g B
    hf0 hn s ω₀ rfl hω0 τ₁ hτ₁ m₀ hm₀ hm₀e ψ hψ0 hψfin W hW hgen hWord hWψ P₂ hP₂h N₂ ν₂ hη₂ (-1)
    (by rw [hf₂]) (by norm_num) hs₂ τN₂ hτN₂
  refine ⟨Θ₁, hΘ₁adj, Θ₂, hΘ₂adj, m₀, hm₀, fun σ hσ => ⟨?_, ?_⟩⟩
  · -- crepancy: `σ` is the pull-back along the isomorphism `N₁ ≅ T ≅ N₂`
    let := functionFieldAlgebra (ν₁ ≫ sV)
    let := functionFieldAlgebra (ν₂ ≫ sV)
    set α : N₁ ⟶ N₂ := (ν₁ ≫ g) ≫ inv (ν₂ ≫ g) with hαdef
    have hαφ : α ≫ (ν₂ ≫ g) = ν₁ ≫ g := by
      simp only [α, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hα : α ≫ ν₂ ≫ sV = ν₁ ≫ sV := by
      rw [← hgc.comp_eq]
      simp only [← Category.assoc] at hαφ ⊢
      rw [hαφ]
    have hσα : ∀ b, σ b = functionFieldMap α b := by
      intro b
      obtain ⟨a, rfl⟩ :=
        (MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion (ν₂ ≫ g) ⊤ (by simp)).2 b
      rw [hσ a, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply α (ν₂ ≫ g),
        functionFieldMap_congr_hom hαφ]
    have hN₁ : IsNormalVariety k (ν₁ ≫ sV) := ⟨⟨⟩, inferInstance⟩
    have hN₂ : IsNormalVariety k (ν₂ ≫ sV) := ⟨⟨⟩, inferInstance⟩
    have hpair : ∀ (N : Scheme.{0}) [IsIntegral N] [IsLocallyNoetherian N] [IsNormal N]
        [CompactSpace N] (sN : N ⟶ Spec (.of k)) [LocallyOfFiniteType sN],
        IsNormalVariety k sN → topologicalKrullDim N = 1 → ∀ Θ : QDivisor N,
        MMP.Mori.IsPair sN Θ := by
      intro N _ _ _ _ sN _ hNv hdN Θ
      obtain ⟨KN, hKN⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sN hNv
        (n := 1) (by rw [hdN]; rfl)
      refine MMP.Mori.isPair_of_isCanonicalDivisor hNv hKN
        (isQCartier_of_isQFactorial sN (isQFactorial_of_isClosed_genericPoint hNv fun Q =>
          isClosed_singleton_of_ne_genericPoint sN hdN
            (PrimeDivisor.genericPoint_ne_genericPoint Q)) _)
    have hΘ : ∀ (Q₁ : Mori.PrimeDivisor N₁) (Q₂ : Mori.PrimeDivisor N₂),
        Q₂.genericPoint = α Q₁.genericPoint → Θ₂.coeff Q₂ = Θ₁.coeff Q₁ := by
      intro Q₁ Q₂ hQ
      rw [show Θ₂.coeff Q₂ = Θ₂ Q₂ from rfl, show Θ₁.coeff Q₁ = Θ₁ Q₁ from rfl, hΘ₁ Q₁, hΘ₂ Q₂]
      have hpt : (ν₂ ≫ g) Q₂.genericPoint = (ν₁ ≫ g) Q₁.genericPoint := by
        rw [hQ, ← Scheme.Hom.comp_apply, hαφ]
      rw [hpt]
      have hform : Q₁.ordForm τN₁ = Q₂.ordForm τN₂ := by
        have e := ordForm_pluriformPullback_of_isIso α hα (d := 1) hdimN₂
          (functionFieldHomOfEq (ν₁ ≫ sV) (ν₂ ≫ sV) α hα)
          (fun a => functionFieldHomOfEq_apply _ _ _ hα a) Q₁ Q₂ hQ.symm τN₂
        rw [← e]
        congr 1
        have h1 : τN₂ = ((1 : N₂.functionField) • formPow (exteriorPower.ιMulti N₂.functionField 1
            fun _ : Fin 1 => KaehlerDifferential.D k N₂.functionField
              (functionFieldMap (ν₂ ≫ g) s)) 1 : RationalPluriForms (ν₂ ≫ sV) 1 ((1 : ℕ) : ℤ)) := by
          rw [hτN₂, one_smul]
        rw [h1, pluriformPullback_smul_formPow_D (ν₁ ≫ sV) (ν₂ ≫ sV) hdimN₁ hdimN₂ _ _ 1 hs₂ 1,
          map_one, one_smul, hτN₁, functionFieldHomOfEq_apply,
          MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply α (ν₂ ≫ g),
          functionFieldMap_congr_hom hαφ]
      have hfun : N₁.ord (functionFieldMap (ν₁ ≫ g) (ψ ((ν₁ ≫ g) Q₁.genericPoint)))
          Q₁.genericPoint = N₂.ord (functionFieldMap (ν₂ ≫ g) (ψ ((ν₁ ≫ g) Q₁.genericPoint)))
            Q₂.genericPoint := by
        rw [← functionFieldMap_congr_hom hαφ,
          ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply α (ν₂ ≫ g)]
        exact MMP.Positivity.ord_functionFieldMap_of_isIso α Q₁ Q₂ hQ.symm _
      rw [hform, hfun]
    exact isCrepantBirationalMap_of_isIso hN₁ hN₂ hdimN₁ hdimN₂ α hα
      (hpair N₁ (ν₁ ≫ sV) hN₁ hdimN₁ Θ₁) (hpair N₂ (ν₂ ≫ sV) hN₂ hdimN₂ Θ₂) hΘ σ hσα
  · -- residues of vertical adjoint pluriforms
    intro m _ hme Ω hΩ ρ₁ ρ₂ hρ₁ hρ₂
    let := functionFieldAlgebra (ν₁ ≫ sV)
    let := functionFieldAlgebra (ν₂ ≫ sV)
    obtain ⟨U, hηU, φ, hU⟩ := hΩ (genericPoint T)
    obtain ⟨a, -, hΩa⟩ := exists_eq_functionFieldMap_smul_formPow hdimV g hgc.isIso_app hcl B hω0
      τ₁ hτ₁ hhor Ω U hηU φ hU
    have e₁ := IsPoincareResidue.unique_of_isClosedImmersion P₁ hη₁ hρ₁
      (by rw [hΩa]; exact hres₁' m a)
    have e₂ := IsPoincareResidue.unique_of_isClosedImmersion P₂ hη₂ hρ₂
      (by rw [hΩa]; exact hres₂' m a)
    have hε₁ : ((1 : ℤ) : N₁.functionField) ^ m = 1 := by simp
    have hε₂ : ((-1 : ℤ) : N₂.functionField) ^ m = 1 := by
      rw [Int.cast_neg, Int.cast_one]; exact hme.neg_one_pow
    rw [e₁, e₂, hε₁, hε₂, mul_one, mul_one,
      pluriformPullback_smul_formPow_D (ν₁ ≫ sV) (ν₂ ≫ sV) hdimN₁ hdimN₂ _ _ _ hs₂ m]
    simp only [FunctionFieldEquiv.toHom, AlgEquiv.coe_algHom, hσ]
    rfl

end MMP.FourfoldProofs.MmpSurfaceRankOneFloorResidueLinkProof

end

end

section

/-!
# Rank-one surface fibrations and the two-branch residue identification

Let `(V, B)` be a `ℚ`-factorial projective lc surface with reduced floor `C = ⌊B⌋`, and
`g : V ⟶ T` a Mori fibre space onto a normal projective curve for the lowered pair
`(V, B - εC)`, `0 < ε < 1`, which is klt, with `K_V + B` numerically trivial over `T`. Then every
closed fibre of `g` has irreducible support, and the horizontal part of `C` has generic degree one
or two over `T`: it is a section, a bisection, or a pair of sections.

The normalization of a section maps isomorphically onto `T`. In degree two, let `(N, Θ)` be the
normalized adjunction pair of a horizontal floor component: `ν : N ⟶ V` is its normalization and
`Θ` is characterised by residues, for some `m > 0` every point of `N` has a neighbourhood `U` in
`V` with a local generator of `𝒪_V(m(K_V + B))` on `U` whose Poincaré residue generates
`𝒪_N(m(K_N + Θ))` on `ν⁻¹ U`. The deck involution of a bisection, and the identification of two
sections over `T`, are crepant birational maps of these pairs. In every sufficiently divisible
even degree `m`, they identify the residues of every rational `m`-canonical form on `V` whose
adjoint divisor `div Ω + mB` is locally over `T` the pull-back of a principal divisor of `T`: the
residue identification is the identification of the two pull-backs of the same line bundle on
`T`.

## Main results

* `MMP.Fourfold.IsMoriFibreSpace.isIrreducible_fibre_and_horizontalFloor_residue`

## Implementation notes

The source works over `ℂ`; the statement is over an algebraically closed field of characteristic
zero. The generic degree of a horizontal prime divisor `P` is the degree
`[κ(η_P) : κ(η_T)]` of the residue field extension at its generic point. A normalization of `P` is
any finite morphism `ν : N ⟶ V` from a normal integral scheme with image `P` that is an
isomorphism on residue fields at the generic point. A birational map of normalized pairs is
recorded by the pull-back on function fields (`MMP.Fourfold.FunctionFieldEquiv`); it lies over
`T` if it commutes with the pull-backs of rational functions of `T`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.FourfoldProofs.MmpSurfaceRankOneFloorResidueLinkProof in
/-- **Rank-one surface fibres and the two-branch residue identification.** Let `V` be a
`ℚ`-factorial normal projective surface with canonical divisor `K`, `B` a `ℚ`-divisor with
`(V, B)` lc and `C = ⌊B⌋`, `0 < ε < 1` with `(V, B - εC)` klt, and `g : V ⟶ T` a Mori fibre space
for `(V, B - εC)` onto a curve with `K + B ≡_g 0`. Then every closed fibre of `g` has irreducible
support, and the set `H` of horizontal components of `C` is either
* a single `P` of generic degree one whose normalizations map isomorphically onto `T`, or
* a single `P` of generic degree two, every `k(T)`-automorphism of the function field of whose
  normalization is crepant for its normalized adjunction pair, or
* two distinct `P₁, P₂` of generic degree one, whose identification over `T` is crepant for their
  normalized adjunction pairs;
and in the last two cases, for every sufficiently divisible even `m`, these identifications match
the residues `ρᵢ` of every rational `m`-canonical form `Ω` on `V` whose adjoint divisor
`div Ω + mB` is locally on `T` the pull-back of a principal divisor. -/
@[mmp "lem_mmp_surface_rank_one_floor_residue_link"]
public theorem IsMoriFibreSpace.isIrreducible_fibre_and_horizontalFloor_residue
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V T : Scheme.{0}} (sV : V ⟶ Spec (.of k)) (sT : T ⟶ Spec (.of k))
    [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsIntegral T]
    (hdimV : topologicalKrullDim V = 2) (hQ : IsQFactorial sV)
    (K : Divisor V) (hK : K.IsCanonicalDivisor sV 2)
    (B : QDivisor V) (hlc : MMP.Intersection.IsLogCanonicalPair sV B)
    (ε : ℚ) (hε : 0 < ε ∧ ε < 1)
    (hklt : IsKltPair sV (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)))
    (g : V ⟶ T) [IsDominant g]
    (hg : IsMoriFibreSpace sV sT K (B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)) g)
    (hdimT : topologicalKrullDim T = 1)
    (hnum : MMP.Flips.IsNumericallyTrivialOver k sV g
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B))) :
    (∀ t : T, IsClosed ({t} : Set T) → IsIrreducible (g.base ⁻¹' {t})) ∧
    let H : Set (Mori.PrimeDivisor V) :=
      {P | ⌊B.coeff P⌋ ≠ 0 ∧ g.base P.genericPoint = genericPoint T}
    let deg : Mori.PrimeDivisor V → ℕ := fun P =>
      letI := (g.residueFieldMap P.genericPoint).hom.toAlgebra
      Module.finrank (T.residueField (g.base P.genericPoint)) (V.residueField P.genericPoint)
    let IsNormalization : ∀ (P : Mori.PrimeDivisor V) (N : Scheme.{0}), (N ⟶ V) → Prop :=
      fun P N ν => IsFinite ν ∧ Set.range ν.base = (P.support : Set V) ∧
        ∃ _ : IsIntegral N, IsIso (ν.residueFieldMap (genericPoint N))
    let IsAdjunctionBoundary :
        ∀ (N : Scheme.{0}) [IsIntegral N] [IsLocallyNoetherian N] (ν : N ⟶ V), QDivisor N → Prop :=
      fun N _ _ ν Θ => ∃ m : ℕ, 0 < m ∧ ∀ x : N, ∃ U : V.Opens, ν.base x ∈ U ∧
        ∃ τ : RationalPluriForms sV 2 m, GeneratesOn B m U τ ∧
          ∃ ρ : RationalPluriForms (ν ≫ sV) 1 m, IsPoincareResidue sV ν 1 m τ ρ ∧
            GeneratesOn Θ m (ν ⁻¹ᵁ U) ρ
    let IsVerticalAdjoint : ∀ m : ℕ, RationalPluriForms sV 2 m → Prop :=
      fun m Ω => ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ φ : T.functionField,
        GeneratesOn B m (g ⁻¹ᵁ U) (functionFieldMap g φ • Ω)
    (∃ P, H = {P} ∧ deg P = 1 ∧
      ∀ (N : Scheme.{0}) [IsIntegral N] (ν : N ⟶ V), IsNormalization P N ν → IsIso (ν ≫ g)) ∨
    (∃ P, H = {P} ∧ deg P = 2 ∧
      ∀ (N : Scheme.{0}) [IsIntegral N] [IsLocallyNoetherian N] [IsNormal N] (ν : N ⟶ V)
        [IsDominant (ν ≫ g)], IsNormalization P N ν →
        ∃ Θ : QDivisor N, IsAdjunctionBoundary N ν Θ ∧ ∃ m₀ : ℕ, 0 < m₀ ∧
          ∀ σ : FunctionFieldEquiv (ν ≫ sV) (ν ≫ sV),
            (∀ a, σ (functionFieldMap (ν ≫ g) a) = functionFieldMap (ν ≫ g) a) →
            IsCrepantBirationalMap (ν ≫ sV) (ν ≫ sV) Θ Θ σ ∧
            ∀ m : ℕ, m₀ ∣ m → Even m → ∀ Ω : RationalPluriForms sV 2 m, IsVerticalAdjoint m Ω →
              ∀ ρ : RationalPluriForms (ν ≫ sV) 1 m, IsPoincareResidue sV ν 1 m Ω ρ →
                pluriformPullback (ν ≫ sV) (ν ≫ sV)
                  (FunctionFieldEquiv.toHom (ν ≫ sV) (ν ≫ sV) σ) 1 m ρ = ρ) ∨
    (∃ P₁ P₂, P₁ ≠ P₂ ∧ H = {P₁, P₂} ∧ deg P₁ = 1 ∧ deg P₂ = 1 ∧
      ∀ (N₁ : Scheme.{0}) [IsIntegral N₁] [IsLocallyNoetherian N₁] [IsNormal N₁] (ν₁ : N₁ ⟶ V)
        [IsDominant (ν₁ ≫ g)] (N₂ : Scheme.{0}) [IsIntegral N₂] [IsLocallyNoetherian N₂]
        [IsNormal N₂] (ν₂ : N₂ ⟶ V) [IsDominant (ν₂ ≫ g)],
        IsNormalization P₁ N₁ ν₁ → IsNormalization P₂ N₂ ν₂ →
        ∃ Θ₁ : QDivisor N₁, IsAdjunctionBoundary N₁ ν₁ Θ₁ ∧
        ∃ Θ₂ : QDivisor N₂, IsAdjunctionBoundary N₂ ν₂ Θ₂ ∧ ∃ m₀ : ℕ, 0 < m₀ ∧
          ∀ σ : FunctionFieldEquiv (ν₁ ≫ sV) (ν₂ ≫ sV),
            (∀ a, σ (functionFieldMap (ν₂ ≫ g) a) = functionFieldMap (ν₁ ≫ g) a) →
            IsCrepantBirationalMap (ν₁ ≫ sV) (ν₂ ≫ sV) Θ₁ Θ₂ σ ∧
            ∀ m : ℕ, m₀ ∣ m → Even m → ∀ Ω : RationalPluriForms sV 2 m, IsVerticalAdjoint m Ω →
              ∀ (ρ₁ : RationalPluriForms (ν₁ ≫ sV) 1 m) (ρ₂ : RationalPluriForms (ν₂ ≫ sV) 1 m),
                IsPoincareResidue sV ν₁ 1 m Ω ρ₁ → IsPoincareResidue sV ν₂ 1 m Ω ρ₂ →
                pluriformPullback (ν₁ ≫ sV) (ν₂ ≫ sV)
                  (FunctionFieldEquiv.toHom (ν₁ ≫ sV) (ν₂ ≫ sV) σ) 1 m ρ₂ = ρ₁) := by
  classical
  obtain ⟨hVv, hVproj⟩ := (Mori.isProjectiveVariety_iff k sV).mp hg.isProjectiveVariety
  have : IsProper sV := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hVproj).2
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have hgc := hg.isContraction
  obtain ⟨hTv, hTn⟩ := hgc.isNormalVariety_target
  have : IsNormal T := hTn
  have : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  have : IsSeparated sT := hTv.toIsSeparated
  have : QuasiCompact sT := hTv.toQuasiCompact
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsProper g :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hgc.isProjectiveMorphism).2
  refine ⟨isIrreducible_fibre_of_isMoriFibreSpace sV sT hdimV hQ hg hdimT, ?_⟩
  intro H deg IsNormalization IsAdjunctionBoundary IsVerticalAdjoint
  have hc := horizontalFloor_cases sV sT hdimV hQ K hK B hlc ε hε g hg hdimT hnum
  dsimp only at hc
  rcases hc with ⟨P, hH, hd⟩ | ⟨P, hH, hd⟩ | ⟨P₁, P₂, hne, hH, hd₁, hd₂⟩
  · refine Or.inl ⟨P, hH, hd, fun N _ ν hν => ?_⟩
    obtain ⟨hfin, hrange, hI, hres⟩ := hν
    have hP : P ∈ H := by rw [show H = {P} from hH]; rfl
    exact isIso_comp_of_finrank_eq_one sV sT hTv hVv hdimV hdimT g hgc.comp_eq P hP.2 hd ν
      hrange hres
  · exact Or.inr (Or.inl ⟨P, hH, hd,
      bisection_clause sV sT hdimV hQ K hK B hlc ε hε hklt g hg hdimT hnum P hH hd⟩)
  · exact Or.inr (Or.inr ⟨P₁, P₂, hne, hH, hd₁, hd₂,
      twoSections_clause sV sT hdimV hQ K hK B hlc ε hε hklt g hg hdimT hnum P₁ P₂ hne hH hd₁
        hd₂⟩)

end MMP.Fourfold

end
