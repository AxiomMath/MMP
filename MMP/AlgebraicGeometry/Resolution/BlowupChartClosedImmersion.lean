module
public import MMP.AlgebraicGeometry.Resolution.Blowup.Charts
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.Derivative
public import StacksFrontier.AlgebraicGeometry.Descent.IdealSheafFpqcDescent
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.AlgebraicGeometry.MMP.Steps
public import StacksFrontier.AlgebraicGeometry.IdealSheafSequence.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaMap.Consequence
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.Basic

/-!
# Foundational lemmas: blow-up charts, intersection numbers, derivations, valuations, descent

This file collects the following independent foundational results used throughout the
minimal model programme.

* A blow-up chart `U_ℓ = D_+(x_ℓ)` of the blow-up of `X` along an ideal sheaf generated on `U`
  by `x_1, …, x_r` is a closed subscheme of `𝔸^{r-1}_U`, cut out by the fractions `x_i / x_ℓ`.
* Intersection numbers `(L₁ ⋯ L_d · Z)` are invariant under restriction to a closed subscheme
  containing `Z`.
* For `X` smooth over `k` and a field extension `L / k`, derivations and first derivative ideals
  commute with the base change `X_L → X`.
* The restriction of a nontrivial discrete valuation through a finite field extension is again
  discrete, with finite ramification index and finite residue field extension.
* Closed subschemes descend along flat, surjective, quasi-compact morphisms.
* An `ℝ`-Cartier divisor is nef iff the closed cone of curves lies in `D_{≥0}`.
* On a smooth variety, `0 ⟶ 𝒪_Y(N) ⟶ 𝒪_Y(N + D) ⟶ 𝒪_Y(N + D)|_Z ⟶ 0` is short exact for a
  Cartier divisor `N` and a reduced closed subscheme `Z` covered by the prime divisors it contains,
  `D` being their sum; in particular for `Z = D` a prime divisor.
* In a regular local ring of dimension `n ≥ 1`, `dim 𝔪^k/𝔪^{k+1} = (k + n - 1).choose (n - 1)`.

## Main results

* `MMP.Flips.ResolutionInputs.isClosedImmersion_homOfVector_chartFraction`
* `MMP.Mori.sheafIntersectionNumber_comp_eq_of_iso`
* `MMP.Resolution.derivativeIdeal_comap_pullback_fst`
* `MMP.Valuation.isRankOneDiscrete_and_relIndex_ne_zero_and_finite_residueField_of_hasExtension`
* `MMP.Foundation.existsUnique_comap_eq_of_comap_fst_eq_comap_snd`
* `MMP.Mori.KCartierDivisor.isNef_iff_closedConeOfCurves_subset_nonnegHalfspace`
* `MMP.Mori.Divisor.IsCartier.shortExact_divisorialSheafInclusion_restriction_of_isReduced`
* `MMP.Mori.Divisor.IsCartier.shortExact_divisorialSheafInclusion_restriction`
* `MMP.Foundation.finrank_pow_maximalIdeal_quotient_smul_top`

## Implementation notes

The chart morphism lands in the relative affine space `𝔸(ι; U)`, which is `U ×_k 𝔸^{r-1}_k` when
`U` lives over a field `k`. Intersection numbers are those of invertible sheaves
(`MMP.Mori.sheafIntersectionNumber`); Cartier divisors are the case `L_t = 𝒪_X(L_t)`. The sheaf
of derivations is read on affine opens, where its sections are `Derivation k 𝒪_X(W) 𝒪_X(W)`.
Closed subschemes are encoded by `AlgebraicGeometry.Scheme.IdealSheafData`. The restriction
`𝒪_Y(N + D)|_Z` is read on `Y` as `i_* i^* 𝒪_Y(N + D)`, the restriction map being the unit of
`i^* ⊣ i_*`. The graded piece `𝔪^k/𝔪^{k+1}` is written `↥(𝔪 ^ k) ⧸ 𝔪 • ⊤`.

## References

* [J. Kollár, *Lectures on resolution of singularities*], 3.60 and Def. 3.73
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.33–1.34, 3.9
-/

@[expose] public section

universe u

section

open CategoryTheory AlgebraicGeometry MMP.Resolution

namespace MMP.Flips.ResolutionInputs

variable {X : Scheme.{u}} {I : X.IdealSheafData}

private theorem presheaf_map_homOfLE_refl_apply (c : BlowupChartData I) (s : Γ(X, c.U)) :
    (X.presheaf.map (homOfLE (le_refl c.U)).op).hom s = s := by
  rw [show (homOfLE (le_refl c.U)).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]; rfl

/-- The chart presentation read in the localization `Γ(X, U)_{x_ℓ}`. -/
private theorem exists_chartPresentation_eq_aeval (c : BlowupChartData I) (hU : IsAffineOpen c.U)
    (ℓ : Fin c.r) :
    ∃ (Θ : Γ(blowUp I, c.chart ℓ) →+* Localization.Away
        ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x ℓ))),
      Function.Injective Θ ∧
      (∀ t, Θ t ∈ affineBlowupAlgebra (I.ideal ⟨c.U, hU⟩)
        ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x ℓ)) (Localization.Away
        ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x ℓ)))) ∧
      (∀ y ∈ affineBlowupAlgebra (I.ideal ⟨c.U, hU⟩)
        ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x ℓ)) (Localization.Away
        ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x ℓ))), ∃ t, Θ t = y) ∧
      Θ.comp (chartPresentation c ℓ) =
        (MvPolynomial.aeval (R := Γ(X, c.U)) fun i : {i : Fin c.r // i ≠ ℓ} =>
          IsLocalization.mk' (Localization.Away
            ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x ℓ))) (c.x i.1)
            (⟨_, Submonoid.mem_powers _⟩ : Submonoid.powers
              ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x ℓ)))).toRingHom := by
  set V : X.affineOpens := ⟨c.U, hU⟩
  set a0 : I.ideal V := ⟨_, c.restrict_mem_ideal V le_rfl ℓ⟩
  have hO := chart_eq_blowUpChartOpen c hU ℓ
  set e := blowUpChartRingIso I V a0
  let ρ : Γ(blowUp I, c.chart ℓ) ≅ Γ(blowUp I, (blowUpChartOpen I V a0).1) :=
    (blowUp I).presheaf.mapIso (eqToIso hO.symm).op
  let E : Γ(blowUp I, c.chart ℓ) ≃+* blowUpAffineChartRing I V a0 :=
    (ρ ≪≫ e).commRingCatIsoToRingEquiv
  let Θ : Γ(blowUp I, c.chart ℓ) →+* Localization.Away (a0 : Γ(X, V.1)) :=
    (Subalgebra.val _).toRingHom.comp E.toRingHom
  have hmor : (blowUpToBase I).appLE c.U (c.chart ℓ) (c.chart_le ℓ) ≫ ρ.hom ≫ e.hom =
      CommRingCat.ofHom (algebraMap Γ(X, V.1) (blowUpAffineChartRing I V a0)) := by
    rw [← Category.assoc]
    have h2 : ((blowUpToBase I).appLE c.U (c.chart ℓ) (c.chart_le ℓ) ≫ ρ.hom) =
        blowUpChartMap I V a0 := Scheme.Hom.appLE_map _ _ _
    rw [h2, blowUpChartMap_comp_ringIso]
  have hpull : ∀ s : Γ(X, c.U), E (chartPullbackHom c ℓ s) =
      algebraMap Γ(X, V.1) (blowUpAffineChartRing I V a0) s :=
    fun s => congrArg (fun φ => φ.hom s) hmor
  have hpull' : ∀ s : Γ(X, c.U), Θ (chartPullbackHom c ℓ s) =
      algebraMap Γ(X, V.1) (Localization.Away (a0 : Γ(X, V.1))) s := by
    intro s
    simp only [Θ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hpull]
    rfl
  refine ⟨Θ, ?_, fun t => (E t).2, fun y hy => ?_, ?_⟩
  · exact Subtype.val_injective.comp E.injective
  · refine ⟨E.symm ⟨y, hy⟩, ?_⟩
    simp only [Θ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
    rfl
  · refine MvPolynomial.ringHom_ext (fun s => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, chartPresentation, MvPolynomial.eval₂Hom_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C, hpull']
      rfl
    · simp only [RingHom.comp_apply, chartPresentation, MvPolynomial.eval₂Hom_X',
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
      rw [IsLocalization.eq_mk'_iff_mul_eq]
      have h := congrArg Θ (chartPullback_eq_chartFraction_mul c ℓ i.1)
      have hc : ∀ s, c.chartPullback ℓ s = chartPullbackHom c ℓ s := fun _ => rfl
      rw [hc, hc, map_mul, hpull', hpull'] at h
      have hcl : algebraMap Γ(X, V.1) (Localization.Away (a0 : Γ(X, V.1))) (c.x ℓ) =
          algebraMap Γ(X, V.1) (Localization.Away (a0 : Γ(X, V.1))) (a0 : Γ(X, V.1)) :=
        congrArg _ (presheaf_map_homOfLE_refl_apply c (c.x ℓ)).symm
      rw [hcl] at h
      exact h.symm

/-- Over an affine open, the chart presentation is surjective, for arbitrary generators. -/
private theorem chartPresentation_surjective (c : BlowupChartData I) (hU : IsAffineOpen c.U)
    (ℓ : Fin c.r) : Function.Surjective (chartPresentation c ℓ) := by
  set a := (X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x ℓ)
  obtain ⟨Θ, hinj, hmemΘ, -, hcomp⟩ := exists_chartPresentation_eq_aeval c hU ℓ
  have ha0v' : a = c.x ℓ := presheaf_map_homOfLE_refl_apply c (c.x ℓ)
  let b : {i : Fin c.r // i ≠ ℓ} → Γ(X, c.U) := fun i => c.x i.1
  have hI : I.ideal ⟨c.U, hU⟩ = Ideal.span (insert a (Set.range b)) := by
    rw [c.generates ⟨c.U, hU⟩ le_rfl]
    congr 1
    ext y
    simp only [presheaf_map_homOfLE_refl_apply, Set.mem_range, Set.mem_insert_iff, ha0v', b]
    constructor
    · rintro ⟨i, rfl⟩
      by_cases hi : i = ℓ
      · exact Or.inl (by rw [hi])
      · exact Or.inr ⟨⟨i, hi⟩, rfl⟩
    · rintro (rfl | ⟨i, rfl⟩)
      · exact ⟨ℓ, rfl⟩
      · exact ⟨i.1, rfl⟩
  set φ : MvPolynomial {i : Fin c.r // i ≠ ℓ} Γ(X, c.U) →ₐ[Γ(X, c.U)] Localization.Away a :=
    MvPolynomial.aeval (fun i =>
      IsLocalization.mk' (Localization.Away a) (b i)
        (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a))
  have hφ : ∀ i, φ (MvPolynomial.X i) * algebraMap _ (Localization.Away a) a =
      algebraMap _ (Localization.Away a) (b i) := by
    intro i
    simp only [φ, MvPolynomial.aeval_X]
    exact IsLocalization.mk'_spec _ _ _
  obtain ⟨hrange, -⟩ := Ideal.range_eq_affineBlowup_and_ker_eq_saturation hI φ hφ
  have haI : a ∈ I.ideal ⟨c.U, hU⟩ := hI ▸ Ideal.subset_span (Set.mem_insert _ _)
  intro t
  have hmem : Θ t ∈ Stacks.AffineBlowup.affineBlowupAlgebra (R := Γ(X, c.U))
      (I.ideal ⟨c.U, hU⟩) a haI := by
    rw [Stacks.AffineBlowup.affineBlowupAlgebra_eq_affineBlowupAlgebraAway _ _ haI,
      affineBlowupAlgebraAway_eq_affineBlowupAlgebra]
    exact hmemΘ t
  rw [Stacks.AffineBlowup.mem_affineBlowupAlgebra haI] at hmem
  obtain ⟨p, hp⟩ : Θ t ∈ Set.range φ := by rwa [hrange]
  refine ⟨p, hinj ?_⟩
  rwa [← RingHom.comp_apply, hcomp]

/-- A morphism is a closed immersion if the target has an affine open cover over each member of
which the preimage is affine and the restriction map on sections is surjective. -/
private theorem isClosedImmersion_of_iSup_eq_top {Y Z : Scheme.{u}} (f : Y ⟶ Z) {ι : Type*}
    (W : ι → Z.affineOpens) (hW : ⨆ i, (W i : Z.Opens) = ⊤)
    (h : ∀ i, IsAffineOpen (f ⁻¹ᵁ (W i : Z.Opens)) ∧ Function.Surjective (f.app (W i))) :
    IsClosedImmersion f := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) _ hW fun i => ?_
  have : IsAffine (f ⁻¹ᵁ (W i : Z.Opens)).toScheme := (h i).1
  have : IsAffine (W i : Z.Opens).toScheme := (W i).2
  refine IsClosedImmersion.of_surjective_of_isAffine _ ?_
  rw [Scheme.Hom.appTop, morphismRestrict_app]
  have hs : Function.Surjective (f.app ((W i : Z.Opens).ι ''ᵁ ⊤)) := by
    rw [Scheme.Opens.ι_image_top]
    exact (h i).2
  exact (ConcreteCategory.bijective_of_isIso (Y.presheaf.map (eqToHom _).op)).2.comp hs

/-- The chart data `c` restricted to an open `V ⊆ U`. -/
private abbrev restrictData (c : BlowupChartData I) (V : X.Opens) (hV : V ≤ c.U) :
    BlowupChartData I where
  U := V
  r := c.r
  x i := (X.presheaf.map (homOfLE hV).op).hom (c.x i)
  generates W h := by
    rw [c.generates W (h.trans hV)]
    congr 1
    ext y
    simp only [Set.mem_range]
    refine exists_congr fun i => ?_
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    rfl

private theorem res_res {A B C : X.Opens} (h₁ : A ≤ B) (h₂ : B ≤ C) (s : Γ(X, C)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom s) =
      (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]; rfl

private theorem blowUpChartOpen_congr (W : X.affineOpens) (a b : I.ideal W)
    (h : (a : Γ(X, W.1)) = b) : blowUpChartOpen I W a = blowUpChartOpen I W b := by
  rw [Subtype.ext h]

private theorem chart_restrictData (c : BlowupChartData I) (V : X.Opens) (hV : V ≤ c.U)
    (ℓ : Fin c.r) :
    (restrictData c V hV).chart ℓ = c.chart ℓ ⊓ blowUpToBase I ⁻¹ᵁ V := by
  apply le_antisymm
  · refine iSup₂_le fun W h => le_inf ?_ ?_
    · rw [blowUpChartOpen_congr W _ ⟨_, c.restrict_mem_ideal W (h.trans hV) ℓ⟩
        (res_res h hV (c.x ℓ))]
      exact le_iSup₂_of_le W (h.trans hV) le_rfl
    · exact (blowUpChartOpen_le I W _).trans fun _ hx => h hx
  · rintro z ⟨hz, hzV⟩
    obtain ⟨W, hzW⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    obtain ⟨h, hzW⟩ := TopologicalSpace.Opens.mem_iSup.mp hzW
    have hzWV : blowUpToBase I z ∈ W.1 ⊓ V :=
      ⟨blowUpChartOpen_le I W _ hzW, hzV⟩
    obtain ⟨W', hW', hzW', hW'le⟩ := exists_isAffineOpen_mem_and_subset hzWV
    have h₁ : W' ≤ W.1 := hW'le.trans inf_le_left
    have h₂ : W' ≤ V := hW'le.trans inf_le_right
    have ha : (X.presheaf.map (homOfLE (show (⟨W', hW'⟩ : X.affineOpens).1 ≤ W.1 from h₁)).op).hom
        ((⟨_, c.restrict_mem_ideal W h ℓ⟩ : I.ideal W) : Γ(X, W.1)) ∈ I.ideal ⟨W', hW'⟩ := by
      rw [res_res]; exact c.restrict_mem_ideal ⟨W', hW'⟩ _ ℓ
    have key := blowUpChartOpen_restrict I (V := ⟨W', hW'⟩) (W := W) h₁
      ⟨_, c.restrict_mem_ideal W h ℓ⟩ ha
    have hz' : z ∈ (blowUpChartOpen I ⟨W', hW'⟩ ⟨_, ha⟩).1 := by
      rw [key]; exact ⟨hzW, hzW'⟩
    rw [blowUpChartOpen_congr ⟨W', hW'⟩ _
      ⟨_, (restrictData c V hV).restrict_mem_ideal ⟨W', hW'⟩ h₂ ℓ⟩
      (by simp only [res_res])] at hz'
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W', hW'⟩,
      TopologicalSpace.Opens.mem_iSup.mpr ⟨h₂, hz'⟩⟩

private theorem chartFraction_restrictData (c : BlowupChartData I) (V : X.Opens) (hV : V ≤ c.U)
    (ℓ i : Fin c.r) :
    chartFraction (restrictData c V hV) ℓ i =
      ((blowUp I).presheaf.map (homOfLE (show (restrictData c V hV).chart ℓ ≤ c.chart ℓ from
        (chart_restrictData c V hV ℓ).le.trans inf_le_left)).op).hom (chartFraction c ℓ i) := by
  have hle : (restrictData c V hV).chart ℓ ≤ c.chart ℓ :=
    (chart_restrictData c V hV ℓ).le.trans inf_le_left
  have hpull : ∀ s : Γ(X, c.U), (restrictData c V hV).chartPullback ℓ
      ((X.presheaf.map (homOfLE hV).op).hom s) =
      ((blowUp I).presheaf.map (homOfLE hle).op).hom (c.chartPullback ℓ s) := by
    intro s
    simp only [BlowupChartData.chartPullback]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_map]
  refine ((restrictData c V hV).existsUnique_chartFraction ℓ i).unique
    (chartPullback_eq_chartFraction_mul (restrictData c V hV) ℓ i) ?_
  change (restrictData c V hV).chartPullback ℓ ((X.presheaf.map (homOfLE hV).op).hom (c.x i)) =
    _ * (restrictData c V hV).chartPullback ℓ ((X.presheaf.map (homOfLE hV).op).hom (c.x ℓ))
  rw [hpull, hpull, chartPullback_eq_chartFraction_mul c ℓ i, map_mul]

private theorem presheaf_map_eq_map_map {T : Scheme.{u}} {A B E : T.Opens}
    (i : Opposite.op A ⟶ Opposite.op E) (j : Opposite.op A ⟶ Opposite.op B)
    (k : Opposite.op B ⟶ Opposite.op E) (x : Γ(T, A)) :
    (T.presheaf.map i).hom x = (T.presheaf.map k).hom ((T.presheaf.map j).hom x) := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

private theorem appLE_eq_of_eq {Y Z : Scheme.{u}} {φ ψ : Y ⟶ Z} (h : φ = ψ) (U : Z.Opens)
    (V : Y.Opens) (e : V ≤ φ ⁻¹ᵁ U) (e' : V ≤ ψ ⁻¹ᵁ U) : φ.appLE U V e = ψ.appLE U V e' := by
  subst h; rfl

private theorem surjective_of_comp_eq {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C]
    [CommRing D] (F : B →+* C) (Φ : A →+* B) (G : D →+* C) (Ψ : A →+* D)
    (h : F.comp Φ = G.comp Ψ) (hG : Function.Surjective G) (hΨ : Function.Surjective Ψ) :
    Function.Surjective F := fun y => by
  obtain ⟨x, rfl⟩ := (hG.comp hΨ) y
  exact ⟨Φ x, by rw [← RingHom.comp_apply, h]; rfl⟩

/-- The morphism `(π, (x_i / x_ℓ)_{i ≠ ℓ}) : U_ℓ → 𝔸^{r-1}_U` of the statement. -/
private noncomputable abbrev chartMorphism (c : BlowupChartData I) (ℓ : Fin c.r) :
    (c.chart ℓ).toScheme ⟶ 𝔸(ULift.{u} {i : Fin c.r // i ≠ ℓ}; c.U.toScheme) :=
  AffineSpace.homOfVector ((blowUpToBase I).resLE c.U (c.chart ℓ) (c.chart_le ℓ))
    fun i => (c.chart ℓ).topIso.inv.hom (chartFraction c ℓ i.down.1)

/-- Over the affine open `𝔸^{r-1}_{V}` for `V ⊆ U` affine, the chart morphism has affine
preimage — the chart of the data restricted to `V` — and is surjective on sections, since the
sections of that chart are generated over `𝒪_X(V)` by the fractions `x_i / x_ℓ`. -/
private theorem chartMorphism_preimage_affine (c : BlowupChartData I) (ℓ : Fin c.r)
    (V' : c.U.toScheme.affineOpens) :
    IsAffineOpen (chartMorphism c ℓ ⁻¹ᵁ
        ((𝔸(ULift.{u} {i : Fin c.r // i ≠ ℓ}; c.U.toScheme) ↘ c.U.toScheme) ⁻¹ᵁ V'.1)) ∧
      Function.Surjective (chartMorphism c ℓ |>.app
        ((𝔸(ULift.{u} {i : Fin c.r // i ≠ ℓ}; c.U.toScheme) ↘ c.U.toScheme) ⁻¹ᵁ V'.1)) := by
  have hcoord := AffineSpace.homOfVector_appTop_coord (n := ULift.{u} {i : Fin c.r // i ≠ ℓ})
    ((blowUpToBase I).resLE c.U (c.chart ℓ) (c.chart_le ℓ))
    fun i => (c.chart ℓ).topIso.inv.hom (chartFraction c ℓ i.down.1)
  set C := c.chart ℓ
  set f := chartMorphism c ℓ
  set p := 𝔸(ULift.{u} {i : Fin c.r // i ≠ ℓ}; c.U.toScheme) ↘ c.U.toScheme
  have hfpι : f ≫ p ≫ c.U.ι = C.ι ≫ blowUpToBase I := by
    rw [← Category.assoc, show f ≫ p = _ from AffineSpace.homOfVector_over _ _,
      Scheme.Hom.resLE_comp_ι]
  set V := c.U.ι ''ᵁ V'.1 with hVdef
  have hV : V ≤ c.U := Scheme.Opens.ι_image_le _ _
  have hVaff : IsAffineOpen V := V'.2.image_of_isOpenImmersion _
  set c' := restrictData c V hV
  set D := c'.chart ℓ
  set O := f ⁻¹ᵁ (p ⁻¹ᵁ V'.1)
  have hO : C.ι ''ᵁ O = D := by
    have hO' : O = (f ≫ p ≫ c.U.ι) ⁻¹ᵁ V := by
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, hVdef,
        Scheme.Hom.preimage_image_eq]
    rw [show D = C ⊓ blowUpToBase I ⁻¹ᵁ V from chart_restrictData c V hV ℓ, hO', hfpι,
      Scheme.Hom.comp_preimage,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  refine ⟨(C.ι.isAffineOpen_iff_of_isOpenImmersion).mp (hO ▸ isAffineOpen_chart c' hVaff ℓ), ?_⟩
  have hOD : O ≤ C.ι ⁻¹ᵁ D := by rw [← hO, Scheme.Hom.preimage_image_eq]
  have hV'V : V'.1 ≤ c.U.ι ⁻¹ᵁ V := by rw [hVdef, Scheme.Hom.preimage_image_eq]
  have ha : Function.Surjective (C.ι.appLE D O hOD) := by
    have : IsIso (homOfLE hO.le).op := by
      rw [show homOfLE hO.le = eqToHom hO from Subsingleton.elim _ _]; infer_instance
    rw [Scheme.Opens.ι_appLE]
    exact (ConcreteCategory.bijective_of_isIso ((blowUp I).presheaf.map (homOfLE hO.le).op)).2
  let Φ : MvPolynomial {i : Fin c.r // i ≠ ℓ} Γ(X, V) →+*
      Γ(𝔸(ULift.{u} {i : Fin c.r // i ≠ ℓ}; c.U.toScheme), p ⁻¹ᵁ V'.1) :=
    MvPolynomial.eval₂Hom (c.U.ι.appLE V V'.1 hV'V ≫ p.app V'.1).hom fun i =>
      ((𝔸(ULift.{u} {i : Fin c.r // i ≠ ℓ}; c.U.toScheme)).presheaf.map
        (homOfLE le_top).op).hom (AffineSpace.coord c.U.toScheme ⟨i⟩)
  refine surjective_of_comp_eq (f.app (p ⁻¹ᵁ V'.1)).hom Φ (C.ι.appLE D O hOD).hom
    (chartPresentation c' ℓ) ?_ ha (chartPresentation_surjective c' hVaff ℓ)
  refine MvPolynomial.ringHom_ext (fun s => ?_) (fun i => ?_)
  · have key : (c.U.ι.appLE V V'.1 hV'V ≫ p.app V'.1) ≫ f.app (p ⁻¹ᵁ V'.1) =
        (blowUpToBase I).appLE V D (c'.chart_le ℓ) ≫ C.ι.appLE D O hOD := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Category.assoc,
        Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_eq_of_eq hfpι _ _ _ _
    simp only [RingHom.comp_apply, Φ, MvPolynomial.eval₂Hom_C, chartPresentation]
    exact congrArg (fun φ => φ.hom s) key
  · simp only [RingHom.comp_apply, Φ, MvPolynomial.eval₂Hom_X', chartPresentation,
      chartFraction_restrictData c V hV ℓ i.1]
    have key : (𝔸(ULift.{u} {i : Fin c.r // i ≠ ℓ}; c.U.toScheme)).presheaf.map
        (homOfLE le_top).op ≫ f.app (p ⁻¹ᵁ V'.1) =
        f.appTop ≫ C.toScheme.presheaf.map (homOfLE le_top).op := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]; rfl
    rw [← CommRingCat.comp_apply, key, CommRingCat.comp_apply, hcoord ⟨i⟩,
      chartFraction_restrictData c V hV ℓ i.1, Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE,
      Scheme.Opens.toScheme_presheaf_map]
    erw [← CommRingCat.comp_apply, ← Functor.map_comp]
    exact presheaf_map_eq_map_map _ _ _ _

/-- **A blow-up chart is a closed subscheme of affine space over the base.** If
`x_1, …, x_r ∈ 𝒪_X(U)` generate the centre on `U`, then for every `ℓ` the morphism
`U_ℓ → 𝔸^{r-1}_U` given by `π` and the fractions `x_i / x_ℓ` (`i ≠ ℓ`,
`MMP.Flips.ResolutionInputs.chartFraction`) is a closed immersion. -/
@[mmp "lem_mmp_foundation_blowup_coordinate_chart_closed_immersion"]
public theorem isClosedImmersion_homOfVector_chartFraction (c : BlowupChartData I) (ℓ : Fin c.r) :
    IsClosedImmersion (AffineSpace.homOfVector (n := ULift.{u} {i : Fin c.r // i ≠ ℓ})
      ((blowUpToBase I).resLE c.U (c.chart ℓ) (c.chart_le ℓ))
      fun i => (c.chart ℓ).topIso.inv.hom (chartFraction c ℓ i.down.1)) := by
  set p := 𝔸(ULift.{u} {i : Fin c.r // i ≠ ℓ}; c.U.toScheme) ↘ c.U.toScheme
  refine isClosedImmersion_of_iSup_eq_top (chartMorphism c ℓ)
    (fun V' : c.U.toScheme.affineOpens => ⟨p ⁻¹ᵁ V'.1, V'.2.preimage p⟩) ?_
    (chartMorphism_preimage_affine c ℓ)
  change ⨆ V' : c.U.toScheme.affineOpens, p ⁻¹ᵁ V'.1 = ⊤
  rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]

end MMP.Flips.ResolutionInputs

end

section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open Stacks.SheafOfModules.Invertible

section Intertwine

variable {A : Type*} [Category A] {B : Type*} [Category B]

/-- A functor `R` carrying the autoequivalence `e` objectwise to `e'` carries the quasi-inverse
of `e` objectwise to that of `e'`. -/
private noncomputable def inverseIntertwineObj (e : A ≌ A) (e' : B ≌ B) (R : A ⥤ B)
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M)) (N : A) :
    R.obj (e.inverse.obj N) ≅ e'.inverse.obj (R.obj N) :=
  e'.unitIso.app (R.obj (e.inverse.obj N)) ≪≫
    e'.inverse.mapIso ((α (e.inverse.obj N)).symm ≪≫ R.mapIso (e.counitIso.app N))

/-- A functor carrying `e` objectwise to `e'` carries every natural iterate of `e` to that of
`e'`. -/
private noncomputable def powNatIntertwineObj (e : A ≌ A) (e' : B ≌ B) (R : A ⥤ B)
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M)) :
    (n : ℕ) → (M : A) →
      R.obj ((e.powNat n).functor.obj M) ≅ (e'.powNat n).functor.obj (R.obj M)
  | 0, M => Iso.refl (R.obj M)
  | 1, M => α M
  | n + 2, M =>
      powNatIntertwineObj e e' R α (n + 1) (e.functor.obj M) ≪≫
        (e'.powNat (n + 1)).functor.mapIso (α M)

/-- A functor carrying `e` objectwise to `e'` carries every integer iterate of `e` to that of
`e'`. -/
private noncomputable def powIntertwineObj (e : A ≌ A) (e' : B ≌ B) (R : A ⥤ B)
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M)) :
    (n : ℤ) → (M : A) →
      R.obj ((e ^ n).functor.obj M) ≅ (e' ^ n).functor.obj (R.obj M)
  | Int.ofNat n, M => powNatIntertwineObj e e' R α n M
  | Int.negSucc n, M =>
      powNatIntertwineObj e.symm e'.symm R
        (fun N => inverseIntertwineObj e e' R α N) (n + 1) M

end Intertwine

/-- Integer tensor powers of invertible modules depend only on the isomorphism class: an
isomorphism `M ≅ N` makes `- ⊗ M` and `- ⊗ N` objectwise isomorphic, and
`powIntertwineObj` carries this to every integer power. -/
private noncomputable def tensorPowerIsoOfIso {X : Scheme.{u}} (M N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (e : M ≅ N) (m : ℤ) :
    tensorPower X.presheaf X.ringCatSheaf.2 M m ≅
      tensorPower X.presheaf X.ringCatSheaf.2 N m :=
  powIntertwineObj
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj M).asEquivalence
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).flip.obj N).asEquivalence (𝟭 _)
    (fun A => ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj A).mapIso e) m
    (SheafOfModules.unit _)

/-- One twisting step `M ↦ M ⊗ L_i^{⊗ n_i}`. -/
private noncomputable abbrev twistStep {X : Scheme.{u}} {r : ℕ} (L : Fin r → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L t)] (n : Fin r → ℤ)
    (M : X.Modules) (i : Fin r) : X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
      (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj M).obj
    (tensorPower X.presheaf X.ringCatSheaf.2 (L i) (n i))

/-- Successive twists of isomorphic modules by isomorphic invertible modules, along any list of
indices, are isomorphic. -/
private noncomputable def foldlTwistIso {X : Scheme.{u}} {r : ℕ} (L L' : Fin r → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L t)]
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L' t)]
    (e : ∀ t, L t ≅ L' t) (n : Fin r → ℤ) :
    (l : List (Fin r)) → {M M' : X.Modules} → (M ≅ M') →
      (l.foldl (twistStep L n) M ≅ l.foldl (twistStep L' n) M')
  | [], _, _, eM => eM
  | i :: l, _, _, eM => foldlTwistIso L L' e n l
      (((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso eM).app _ ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
          (tensorPowerIsoOfIso (L i) (L' i) (e i) (n i)))

/-- Twisting by isomorphic families of invertible modules gives isomorphic modules. -/
private noncomputable def twistedSheafIso {X : Scheme.{u}} {r : ℕ} (F : X.Modules)
    (L L' : Fin r → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L t)]
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L' t)]
    (e : ∀ t, L t ≅ L' t) (n : Fin r → ℤ) :
    twistedSheaf F L n ≅ twistedSheaf F L' n :=
  foldlTwistIso L L' e n _ (Iso.refl F)

/-- Isomorphic coherent sheaves have equal Euler characteristics, also when the structure
morphisms are only equal propositionally. -/
private theorem eulerCharacteristic_eq_of_iso_of_eq (k : Type u) [Field k] {Z : Scheme.{u}}
    {g g' : Z ⟶ Spec (.of k)} (h : g = g') [IsProper g] [IsProper g'] {F G : Z.Modules}
    (hF : F.IsCoherent) (hG : G.IsCoherent) (e : F ≅ G) :
    @eulerCharacteristic k _ Z g _ F hF = @eulerCharacteristic k _ Z g' _ G hG := by
  subst h
  exact eulerCharacteristic_eq_of_iso k g e

/-- **Restriction invariance of intersection numbers.** For a proper `k`-scheme `X`, closed
immersions `i : Z ⟶ Y`, `j : Y ⟶ X` with `dim Z ≤ d`, and invertible sheaves `L_t` on `X`,
`L'_t` on `Y` with `L_t|_Y ≅ L'_t`, the intersection number `(L₁ ⋯ L_d · Z)` on `X` equals
`(L'₁ ⋯ L'_d · Z)` on `Y`. -/
@[mmp "lem_mmp_foundation_cohomological_intersection_restriction"]
public theorem sheafIntersectionNumber_comp_eq_of_iso (k : Type u) [Field k]
    {X Y Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (j : Y ⟶ X) [IsClosedImmersion j] (i : Z ⟶ Y) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    (L : Fin d → X.Modules) [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L t)]
    (L' : Fin d → Y.Modules) [∀ t, SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (L' t)]
    (e : ∀ t, (Scheme.Modules.pullback j).obj (L t) ≅ L' t) :
    sheafIntersectionNumber k f (i ≫ j) d hd L = sheafIntersectionNumber k (j ≫ f) i d hd L' := by
  unfold MMP.Mori.sheafIntersectionNumber
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  exact eulerCharacteristic_eq_of_iso_of_eq k (Category.assoc _ _ _) _ _
    (twistedSheafIso _ _ _ (fun t => ((Scheme.Modules.pullbackComp i j).app (L t)).symm ≪≫
      (Scheme.Modules.pullback i).mapIso (e t)) _)

end MMP.Mori

end

section

open CategoryTheory AlgebraicGeometry Limits TensorProduct KaehlerDifferential

namespace MMP.Resolution

section Algebra

variable {k L A B : Type*} [CommRing k] [CommRing L] [CommRing A] [CommRing B]
  [Algebra k L] [Algebra k A] [Algebra A B] [Algebra L B] [Algebra k B]
  [IsScalarTower k A B] [IsScalarTower k L B] [Algebra.IsPushout k L A B]

/-- Derivations commute with the base change `B = L ⊗_k A`, when `Ω_{A/k}` is finitely presented
and `B` is flat over `A`. -/
private theorem exists_tensorDerivationEquiv [Module.Flat A B]
    [Module.FinitePresentation A Ω[A⁄k]] :
    ∃ e : B ⊗[A] Derivation k A A ≃ₗ[B] Derivation L B B,
      ∀ (δ : Derivation k A A) (a : A), e (1 ⊗ₜ δ) (algebraMap A B a) = algebraMap A B (δ a) := by
  let e1 : B ⊗[A] Derivation k A A ≃ₗ[B] B ⊗[A] (Ω[A⁄k] →ₗ[A] A) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (linearMapEquivDerivation k A (M := A)).symm
  let e2 := (Module.FinitePresentation.isBaseChange_map (R := A) (M := Ω[A⁄k]) (N := A) B).equiv
  let e3 : (B ⊗[A] Ω[A⁄k] →ₗ[B] B ⊗[A] A) ≃ₗ[B] (Ω[B⁄L] →ₗ[B] B) :=
    LinearEquiv.arrowCongr (tensorKaehlerEquiv k L A B)
      (TensorProduct.AlgebraTensorModule.rid A B B)
  refine ⟨e1 ≪≫ₗ e2 ≪≫ₗ e3 ≪≫ₗ linearMapEquivDerivation L B (M := B), fun δ a => ?_⟩
  have h1 : (tensorKaehlerEquiv k L A B).symm (D L B (algebraMap A B a)) = 1 ⊗ₜ D k A a := by
    rw [LinearEquiv.symm_apply_eq, tensorKaehlerEquiv_tmul_D, one_smul]
  simp [e1, e2, e3, IsBaseChange.equiv_tmul, h1, Algebra.smul_def]

include k in
/-- Every element of the extension `J B` of an ideal `J ⊆ A` to `B = L ⊗_k A` lies in the
`L`-span of the image of `J`. -/
private theorem mem_span_of_mem_map (J : Ideal A) {f : B} (hf : f ∈ J.map (algebraMap A B)) :
    f ∈ Submodule.span L (algebraMap A B '' J) := by
  let S := Submodule.span L (algebraMap A B '' (J : Set A))
  have hS : ∀ b : B, ∀ s ∈ S, b * s ∈ S := by
    intro b
    refine (Algebra.IsPushout.out (R := k) (S := L) (R' := A) (S' := B)).inductionOn b
      (motive := fun b => ∀ s ∈ S, b * s ∈ S) ?_ ?_ ?_
    · intro a s hs
      refine Submodule.span_induction ?_ (by simp) (fun x y _ _ hx hy => by
        rw [mul_add]; exact S.add_mem hx hy) (fun l x _ hx => by
        rw [mul_smul_comm]; exact S.smul_mem l hx) hs
      rintro _ ⟨j, hj, rfl⟩
      simp only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', ← map_mul]
      exact Submodule.subset_span ⟨a * j, J.mul_mem_left a hj, rfl⟩
    · intro l b hb s hs
      rw [smul_mul_assoc]
      exact S.smul_mem l (hb s hs)
    · intro b₁ b₂ h₁ h₂ s hs
      rw [add_mul]
      exact S.add_mem (h₁ s hs) (h₂ s hs)
  let J' : Ideal B :=
    { carrier := S
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      smul_mem' := fun b s hs => hS b s hs }
  exact (Ideal.map_le_iff_le_comap.mpr fun j hj => Submodule.subset_span ⟨j, hj, rfl⟩ :
    J.map (algebraMap A B) ≤ J') hf

/-- First derivative ideals commute with the base change `B = L ⊗_k A`. -/
private theorem derivativeIdealOfRing_map [Module.Flat A B]
    [Module.FinitePresentation A Ω[A⁄k]] (J : Ideal A) :
    MMP.Resolution.derivativeIdealOfRing L (J.map (algebraMap A B)) =
      (MMP.Resolution.derivativeIdealOfRing k J).map (algebraMap A B) := by
  obtain ⟨e, he⟩ := exists_tensorDerivationEquiv (k := k) (L := L) (A := A) (B := B)
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨δ', f, hf, rfl⟩
    obtain ⟨x, rfl⟩ := e.surjective δ'
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, Derivation.add_apply]; exact Ideal.add_mem _ hx hy
    | tmul b δ =>
      have hb : b ⊗ₜ[A] δ = b • (1 ⊗ₜ[A] δ) := by rw [smul_tmul', smul_eq_mul, mul_one]
      rw [hb, map_smul, Derivation.smul_apply, smul_eq_mul]
      refine Ideal.mul_mem_left _ b ?_
      refine Submodule.span_induction ?_ (by simp) (fun x y _ _ hx hy => by
        rw [map_add]; exact Ideal.add_mem _ hx hy) (fun l x _ hx => by
        rw [Derivation.map_smul, Algebra.smul_def]; exact Ideal.mul_mem_left _ _ hx)
        (mem_span_of_mem_map (k := k) J hf)
      rintro _ ⟨j, hj, rfl⟩
      rw [he]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨δ, j, hj, rfl⟩)
  · refine Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr ?_)
    rintro _ ⟨δ, j, hj, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, ← he]
    exact Ideal.subset_span ⟨_, _, Ideal.mem_map_of_mem _ hj, rfl⟩

end Algebra

section Scheme

variable {k L : Type u} [Field k] [Field L] [Algebra k L] {X : Scheme.{u}}
  (sX : X ⟶ Spec (.of k))

/-- Over an affine open `W ⊆ X`, the sections of `X_L` over `p⁻¹W` are the pushout of
`𝒪_X(W)` and `L` over `k`. -/
private theorem isPushout_sections (W : X.affineOpens) :
    IsPushout (CommRingCat.ofHom (algebraMap k L))
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ W.1 (by simp))
      ((Scheme.ΓSpecIso (.of L)).inv ≫
        (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))).appLE ⊤
        ((pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1) (by simp))
      ((pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))).app W.1) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  set p := pullback.fst sX g
  have : IsAffine W.1 := W.2
  have h := ((isPullback_morphismRestrict p W.1).paste_vert (IsPullback.of_hasPullback sX g)).flip
  refine (isPushout_appTop_of_isPullback h).of_iso (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _)
    W.1.topIso (p ⁻¹ᵁ W.1).topIso (Scheme.ΓSpecIso_naturality _) ?_ ?_ ?_
  · simp [Scheme.Opens.topIso_hom, Scheme.Hom.appLE]
    exact (Category.assoc _ _ _).trans (congrArg _ (X.presheaf.map_comp _ _).symm)
  · simp [Scheme.Opens.topIso_hom, Scheme.Hom.appLE]
    exact (Category.assoc _ _ _).trans (congrArg _ ((pullback sX g).presheaf.map_comp _ _).symm)
  · simp [Scheme.Opens.topIso_hom, Scheme.Hom.appLE, morphismRestrict_app]
    refine (Category.assoc _ _ _).trans
      ((congrArg _ ((pullback sX g).presheaf.map_comp _ _).symm).trans ?_)
    exact (congrArg _ (congrArg _ (Subsingleton.elim _ _))).trans (p.naturality _).symm

/-- The base change of derivations and of first derivative ideals over an affine open `W ⊆ X`
of a scheme locally of finite type over `k`. -/
private theorem sections_baseChange [LocallyOfFiniteType sX] (W : X.affineOpens) :
    letI := MMP.Mori.sectionAlgebra sX W.1
    letI := MMP.Mori.sectionAlgebra
      (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      ((pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1)
    letI := ((pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))).app W.1).hom
        |>.toAlgebra
    (∃ e : Γ(Limits.pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k L))),
              (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1)
              ⊗[Γ(X, W.1)]
            Derivation k Γ(X, W.1) Γ(X, W.1)
            ≃ₗ[Γ(Limits.pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k L))),
              (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1)]
            Derivation L Γ(Limits.pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k L))),
              (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1)
              Γ(Limits.pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k L))),
              (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1),
        ∀ (δ : Derivation k Γ(X, W.1) Γ(X, W.1)) (a : Γ(X, W.1)),
          e (1 ⊗ₜ δ) (algebraMap _ _ a) = algebraMap _ _ (δ a)) ∧
    ∀ J : Ideal Γ(X, W.1),
      MMP.Resolution.derivativeIdealOfRing L
          (J.map ((pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))).app W.1).hom) =
        (MMP.Resolution.derivativeIdealOfRing k J).map
          ((pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))).app W.1).hom := by
  letI := MMP.Mori.sectionAlgebra sX W.1
  letI := MMP.Mori.sectionAlgebra
    (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    ((pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1)
  letI := ((pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))).app W.1).hom
        |>.toAlgebra
  have hP := isPushout_sections (L := L) sX W
  letI : Algebra k Γ(Limits.pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k L))),
      (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1) :=
    ((algebraMap L _).comp (algebraMap k L)).toAlgebra
  haveI : IsScalarTower k L Γ(Limits.pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k L))),
      (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k Γ(X, W.1)
      Γ(Limits.pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k L))),
      (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1) :=
    IsScalarTower.of_algebraMap_eq fun c => (congrArg (fun φ => φ.hom c) hP.w)
  haveI : Algebra.IsPushout k L Γ(X, W.1)
      Γ(Limits.pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k L))),
      (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1) :=
    CommRingCat.isPushout_iff_isPushout.mp hP
  haveI : Module.Flat Γ(X, W.1)
      Γ(Limits.pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k L))),
      (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1) :=
    Module.Flat.isBaseChange (R := k) (M := L) (S := Γ(X, W.1)) (N := Γ(Limits.pullback sX
      (Spec.map (CommRingCat.ofHom (algebraMap k L))),
      (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1))
      (Algebra.IsPushout.symm (inferInstance : Algebra.IsPushout k L Γ(X, W.1) _)).out
  haveI : Algebra.FinitePresentation k Γ(X, W.1) :=
    Algebra.FinitePresentation.of_finiteType.mp (MMP.Mori.finiteType_sectionAlgebra sX W.2)
  exact ⟨exists_tensorDerivationEquiv (k := k), derivativeIdealOfRing_map⟩

end Scheme

/-- **Derivations and first derivative ideals commute with extension of the ground field.**
Let `X` be smooth over a field `k`, `L` a field extension of `k` and
`p : X ×_{Spec k} Spec L → X` the first projection. Then over every affine open `W ⊆ X` the
canonical map `𝒪(p⁻¹W) ⊗_{𝒪(W)} Der_k(𝒪(W)) → Der_L(𝒪(p⁻¹W))`, `1 ⊗ δ ↦ δ_L` with
`δ_L ∘ p^♯ = p^♯ ∘ δ`, is an isomorphism, and for every ideal sheaf `I` on `X`,
`D(p^*I) = p^*D(I)`. -/
@[mmp "lem_mmp_foundation_derivative_ideal_field_extension"]
public theorem derivativeIdeal_comap_pullback_fst {k L : Type u} [Field k] [Field L]
    [Algebra k L] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] :
    (∀ W : X.affineOpens,
      letI := MMP.Mori.sectionAlgebra sX W.1
      letI := MMP.Mori.sectionAlgebra
        (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k L))))
        ((pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1)
      letI := ((pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))).app W.1).hom
        |>.toAlgebra
      ∃ e : Γ(pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k L))),
              (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1)
              ⊗[Γ(X, W.1)]
            Derivation k Γ(X, W.1) Γ(X, W.1)
            ≃ₗ[Γ(pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k L))),
              (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1)]
            Derivation L Γ(pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k L))),
              (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1)
              Γ(pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k L))),
              (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ⁻¹ᵁ W.1),
        ∀ (δ : Derivation k Γ(X, W.1) Γ(X, W.1)) (a : Γ(X, W.1)),
          e (1 ⊗ₜ δ) (algebraMap _ _ a) = algebraMap _ _ (δ a)) ∧
    ∀ I : X.IdealSheafData,
      derivativeIdeal (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k L))))
          (I.comap (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L))))) =
        (derivativeIdeal sX I).comap
          (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
  refine ⟨fun W => (sections_baseChange sX W).1, fun I => ?_⟩
  set g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  set p := pullback.fst sX g
  haveI : IsAffineHom p := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsAffineHom) (IsPullback.of_hasPullback sX g).flip inferInstance
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun W : X.affineOpens => ⟨p ⁻¹ᵁ W.1, W.2.preimage p⟩) ?_ fun W => ?_
  · refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨W, hW, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top (p x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW⟩, hx⟩
  · rw [MMP.Resolution.derivativeIdeal_ideal,
      Stacks.IdealSheaf.ideal_comap_appLE _ p W ⟨_, W.2.preimage p⟩ le_rfl,
      MMP.Resolution.derivativeIdeal_ideal, ← Scheme.Hom.app_eq_appLE]
    unfold MMP.Resolution.sectionDerivativeIdeal
    rw [Stacks.IdealSheaf.ideal_comap_appLE _ p W ⟨_, W.2.preimage p⟩ le_rfl,
      ← Scheme.Hom.app_eq_appLE]
    exact (sections_baseChange sX W).2 (I.ideal W)

end MMP.Resolution

end

namespace MMP.Valuation

open IsLocalRing

/-- A nontrivial subgroup of the cyclic subgroup generated by `γ` has finite index in it. -/
private lemma relIndex_zpowers_ne_zero {G : Type*} [Group G] {γ : G} {H : Subgroup G}
    (hH : H ≤ Subgroup.zpowers γ) (h : H ≠ ⊥) : H.relIndex (Subgroup.zpowers γ) ≠ 0 := by
  obtain ⟨⟨x, hxH⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hH hxH)
  have hn : n ≠ 0 := by rintro rfl; exact hx1 (by ext; simp)
  rw [Subgroup.relIndex]
  have : Finite (Subgroup.zpowers γ ⧸ H.subgroupOf (Subgroup.zpowers γ)) := by
    refine Finite.of_surjective
      (fun i : Fin n.natAbs => (QuotientGroup.mk (⟨γ ^ (i : ℤ), Subgroup.zpow_mem_zpowers _ _⟩ :
        Subgroup.zpowers γ) : Subgroup.zpowers γ ⧸ H.subgroupOf (Subgroup.zpowers γ))) ?_
    intro q
    obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have h0 : 0 ≤ m % n := Int.emod_nonneg m hn
    have h1 : m % n < n.natAbs := by
      have := Int.emod_lt m hn; omega
    refine ⟨⟨(m % n).toNat, by omega⟩, ?_⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hmn : ((m % n).toNat : ℤ) = m % n := Int.toNat_of_nonneg h0
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [hmn, ← zpow_neg, ← zpow_add, show -(m % n) + m = n * (m / n) by
      have := Int.emod_add_mul_ediv m n; linarith, zpow_mul]
    exact Subgroup.zpow_mem _ hxH _
  exact Subgroup.index_ne_zero_of_finite

/-- Elements of the valuation ring of `w` whose residues are linearly independent over the
residue field of `vK` are linearly independent over `K`: divide a relation by a coefficient of
largest valuation and reduce. -/
private lemma linearIndependent_of_residue {K L Γ₀ Γ₁ ι : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
    [Fintype ι] (vK : _root_.Valuation K Γ₀) (w : _root_.Valuation L Γ₁) [vK.HasExtension w]
    {b : ι → w.valuationSubring}
    (hb : LinearIndependent (ResidueField vK.valuationSubring)
      fun i => residue w.valuationSubring (b i)) :
    LinearIndependent K fun i => (b i : L) := by
  rw [Fintype.linearIndependent_iff] at hb ⊢
  intro g hg
  by_contra hne
  push Not at hne
  obtain ⟨i0, hi0⟩ := hne
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => vK (g i))
    ⟨i0, Finset.mem_univ _⟩
  have hgj : g j ≠ 0 := by
    rintro h
    have := hj i0 (Finset.mem_univ _)
    rw [h, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact hi0 this
  have hc : ∀ i, g i / g j ∈ vK.valuationSubring := fun i => by
    rw [Valuation.mem_valuationSubring_iff, map_div₀,
      div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff vK).mpr hgj))]
    exact hj i (Finset.mem_univ _)
  let c : ι → vK.valuationSubring := fun i => ⟨g i / g j, hc i⟩
  have hsum : ∑ i, algebraMap vK.valuationSubring w.valuationSubring (c i) * b i = 0 := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul,
      Valuation.HasExtension.coe_algebraMap_valuationSubring_eq, ZeroMemClass.coe_zero]
    change ∑ i, algebraMap K L (g i / g j) * (b i : L) = 0
    simp_rw [map_div₀, div_mul_eq_mul_div, ← Finset.sum_div, ← Algebra.smul_def, hg, zero_div]
  have hres := congrArg (residue w.valuationSubring) hsum
  simp only [map_sum, map_mul, map_zero] at hres
  have := hb (fun i => residue vK.valuationSubring (c i)) (by
    simpa only [Algebra.smul_def,
      Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap] using hres) j
  have hcj : c j = 1 := by ext; simp [c, hgj]
  rw [hcj, map_one] at this
  exact one_ne_zero this

/-- For a finite extension `L / K` and a valuation `w` of `L` extending `vK`, the residue field
of `w` is finite over that of `vK`. -/
private lemma finite_residueField {K L Γ₀ Γ₁ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ₁] (vK : _root_.Valuation K Γ₀) (w : _root_.Valuation L Γ₁)
    [vK.HasExtension w] :
    Module.Finite (ResidueField vK.valuationSubring) (ResidueField w.valuationSubring) := by
  refine Module.rank_lt_aleph0_iff.mp ((rank_le (n := Module.finrank K L) fun s hs => ?_).trans_lt
    Cardinal.natCast_lt_aleph0)
  choose b hb using fun i : s => residue_surjective (i : ResidueField w.valuationSubring)
  simpa using (linearIndependent_of_residue vK w (b := b) (by simpa [hb] using hs)
    ).fintype_card_le_finrank

/-- The restriction of a nontrivial discrete valuation `w` of `L` to a subfield `K` with
`L / K` finite is a nontrivial discrete valuation; the value group of the restriction has finite
index in that of `w`; and the residue field extension is finite. -/
@[mmp "lem_mmp_foundation_finite_extension_valuation_restriction"]
public theorem isRankOneDiscrete_and_relIndex_ne_zero_and_finite_residueField_of_hasExtension
    {K L Γ₀ Γ₁ : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
    (vK : _root_.Valuation K Γ₀) (w : _root_.Valuation L Γ₁) [vK.HasExtension w]
    [w.IsRankOneDiscrete] :
    vK.IsRankOneDiscrete ∧
      (w.comap (algebraMap K L)).valueGroup.relIndex w.valueGroup ≠ 0 ∧
      Module.Finite (ResidueField vK.valuationSubring) (ResidueField w.valuationSubring) := by
  set u := w.comap (algebraMap K L)
  have hequiv : vK.IsEquiv u := Valuation.HasExtension.val_isEquiv_comap
  have hle : u.valueGroup ≤ w.valueGroup := by
    intro y hy
    rw [MonoidWithZeroHom.mem_valueGroup_iff_of_comm] at hy ⊢
    obtain ⟨a, ha, x, hx⟩ := hy
    exact ⟨algebraMap K L a, ha, algebraMap K L x, hx⟩
  -- The restriction is nontrivial: otherwise every `y` with `w y ≠ 0, 1` is transcendental.
  have hnt : u.IsNontrivial := by
    by_contra h
    have : w.IsTrivialOn K := ⟨fun a ha => by
      by_contra h'
      exact h ⟨a, by simpa [u] using ha, h'⟩⟩
    obtain ⟨y, hy0, hy1⟩ := (inferInstance : w.IsNontrivial).exists_val_nontrivial
    exact Valuation.transcendental_of_ne_one K y ((Valuation.ne_zero_iff w).mp hy0) hy1
      (Algebra.IsAlgebraic.isAlgebraic y)
  have hG : Subgroup.zpowers (Valuation.IsRankOneDiscrete.generator w) = w.valueGroup :=
    Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup w
  refine ⟨?_, ?_, finite_residueField vK w⟩
  · haveI : vK.IsNontrivial := hequiv.isNontrivial_iff.mpr hnt
    haveI : IsCyclic w.valueGroup := inferInstance
    haveI : IsCyclic u.valueGroup := Subgroup.isCyclic_of_le hle
    let e : u.valueGroup ≃* MonoidWithZeroHom.valueGroup (vK : K →*₀ Γ₀) :=
      (WithZero.unitsWithZeroEquiv.symm.trans
        (Units.mapEquiv hequiv.symm.orderMonoidIso.toMulEquiv)).trans
        WithZero.unitsWithZeroEquiv
    haveI : IsCyclic (MonoidWithZeroHom.valueGroup (vK : K →*₀ Γ₀)) :=
      isCyclic_of_surjective e.toMonoidHom e.surjective
    exact Valuation.IsRankOneDiscrete.mk' vK
  · rw [← hG]
    refine relIndex_zpowers_ne_zero (hG ▸ hle) fun hbot => ?_
    have : Nontrivial u.valueGroup :=
      (inferInstance : Nontrivial (MonoidWithZeroHom.valueGroup (u : K →*₀ Γ₁)))
    exact not_nontrivial _ (hbot ▸ this)

end MMP.Valuation

section

open CategoryTheory Limits AlgebraicGeometry

namespace MMP.Foundation

/-- An ideal sheaf whose pullback along a flat, surjective, quasi-compact morphism vanishes is
zero. -/
private theorem eq_bot_of_comap_eq_bot {X X' : Scheme} (g : X' ⟶ X)
    [Flat g] [Surjective g] [QuasiCompact g] (K : X.IdealSheafData) (hK : K.comap g = ⊥) :
    K = ⊥ := by
  obtain ⟨h, hh⟩ := (Scheme.IdealSheafData.comap_eq_bot_iff_exists K g).1 hK
  have : IsIso K.subschemeι :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨⟨‹_›, ‹_›⟩, ‹_›⟩
      (hh ▸ inferInstance : IsIso (pullback.snd K.subschemeι g))
  rw [← Scheme.IdealSheafData.ker_subschemeι K]
  exact Scheme.Hom.ker_eq_bot_of_isIso _

/-- Pullback of ideal sheaves along a flat, surjective, quasi-compact morphism reflects `≤`. -/
private theorem le_of_comap_eq {X X' : Scheme} (g : X' ⟶ X)
    [Flat g] [Surjective g] [QuasiCompact g] (J₁ J₂ : X.IdealSheafData)
    (h : J₁.comap g = J₂.comap g) : J₂ ≤ J₁ := by
  have h₁ : J₁.comap J₁.subschemeι = ⊥ :=
    (Scheme.IdealSheafData.comap_eq_bot_iff_exists J₁ _).2 ⟨𝟙 _, by simp⟩
  have h₂ : J₂.comap J₁.subschemeι = ⊥ := by
    apply eq_bot_of_comap_eq_bot (pullback.fst J₁.subschemeι g)
    rw [← Scheme.IdealSheafData.comap_comp, pullback.condition,
      Scheme.IdealSheafData.comap_comp, ← h, ← Scheme.IdealSheafData.comap_comp,
      ← pullback.condition, Scheme.IdealSheafData.comap_comp, h₁,
      Scheme.IdealSheafData.comap_bot]
  obtain ⟨k, hk⟩ := (Scheme.IdealSheafData.comap_eq_bot_iff_exists J₂ _).1 h₂
  calc J₂ = J₂.subschemeι.ker := (Scheme.IdealSheafData.ker_subschemeι J₂).symm
    _ ≤ (k ≫ J₂.subschemeι).ker := Scheme.Hom.le_ker_comp _ _
    _ = J₁ := by rw [hk, Scheme.IdealSheafData.ker_subschemeι]

/-- **fpqc descent of closed subschemes.** If `g : X' ⟶ X` is flat, surjective and
quasi-compact, and `I` is an ideal sheaf on `X'` whose pullbacks along the two projections
`X' ×_X X' ⟶ X'` coincide, then there is a unique ideal sheaf `J` on `X` with
`I = J.comap g`. -/
@[mmp "lem_mmp_foundation_fpqc_closed_subscheme_descent"]
public theorem existsUnique_comap_eq_of_comap_fst_eq_comap_snd {X X' : Scheme} (g : X' ⟶ X)
    [Flat g] [Surjective g] [QuasiCompact g] (I : X'.IdealSheafData)
    (h : I.comap (pullback.fst g g) = I.comap (pullback.snd g g)) :
    ∃! J : X.IdealSheafData, I = J.comap g := by
  have hcov : Presieve.ofArrows (fun _ : PUnit => X') (fun _ => g) ∈
      Scheme.fpqcPrecoverage X := by
    rw [Presieve.ofArrows_pUnit]
    exact g.singleton_mem_fpqcPrecoverage
  obtain ⟨K, hK⟩ := Scheme.IdealSheafData.exists_comap_eq_of_fpqc _ hcov (fun _ => I)
    (fun _ _ => h)
  refine ⟨K, (hK ⟨⟩).symm, fun J hJ => ?_⟩
  have e : J.comap g = K.comap g := hJ.symm.trans (hK ⟨⟩).symm
  exact le_antisymm (le_of_comap_eq g K J e.symm) (le_of_comap_eq g J K e)

end MMP.Foundation

end

section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- `(z · D) = ∑ⱼ cⱼ deg_z 𝒪_X(Dⱼ)` for `D = ∑ⱼ cⱼ Dⱼ`. -/
private theorem coe_intersectionNumber_eq_sum (D : KCartierDivisor ℝ X) :
    ⇑(NumericalCurveClasses.intersectionNumber (sX := sX) D) = fun z =>
      D.sum fun E c => c * NumericalCurveClasses.degree sX
        (MMP.CartierDivisor.sheaf E) z := by
  funext z
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  simp only [NumericalCurveClasses.intersectionNumber_numericalClass,
    NumericalCurveClasses.degree_numericalClass, OneCycle.intersectionNumber,
    OneCycle.intersectionPairing, Finsupp.linearCombination_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, OneCycle.cartierDegree]

/-- The intersection form `z ↦ (z · D)` is continuous for the numerical topology. -/
private theorem continuous_intersectionNumber (D : KCartierDivisor ℝ X) :
    Continuous (NumericalCurveClasses.intersectionNumber (sX := sX) D) := by
  rw [coe_intersectionNumber_eq_sum]
  exact continuous_finset_sum _ fun E _ =>
    continuous_const.mul (NumericalCurveClasses.continuous_degree sX _)

/-- `D_{≥0}` is the pointed cone pulled back from `ℝ_{≥0}` along `z ↦ (z · D)`. -/
private theorem nonnegHalfspace_eq_comap (D : KCartierDivisor ℝ X) :
    KCartierDivisor.nonnegHalfspace sX D =
      ((PointedCone.positive ℝ ℝ).comap (NumericalCurveClasses.intersectionNumber (sX := sX) D) :
        Set (NumericalCurveClasses sX)) := by
  ext z
  exact KCartierDivisor.mem_nonnegHalfspace_iff sX D z

/-- An `ℝ`-Cartier divisor `D` on a proper variety `X` is nef if and only if the closed cone of
curves `NE̅(X)` is contained in the half-space `D_{≥0}`. -/
@[mmp "lem_mmp_foundation_full_field_nef_closed_cone"]
public theorem KCartierDivisor.isNef_iff_closedConeOfCurves_subset_nonnegHalfspace
    [IsProperVariety k sX] (D : KCartierDivisor ℝ X) :
    KCartierDivisor.IsNef k sX D ↔
      (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) ⊆
        KCartierDivisor.nonnegHalfspace sX D := by
  refine ⟨fun hD => ?_, fun h C => ?_⟩
  · rw [coe_closedConeOfCurves, nonnegHalfspace_eq_comap sX]
    refine closure_minimal (Submodule.span_le.2 ?_)
      (isClosed_Ici.preimage (continuous_intersectionNumber sX D))
    rintro _ ⟨C, rfl⟩
    exact hD C
  · exact h (coneOfCurves_le_closedConeOfCurves sX (numericalClass_cycle_mem_coneOfCurves sX C))
      _ rfl

end MMP.Mori

end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MMP.Mori.Divisor

noncomputable section

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

variable (X) in
/-- The sheafification adjunction for presheaves of `𝒪_X`-modules. -/
private abbrev tensorAdj :=
  PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj)

/-- The image of `a ⊗ b` in the sheafified tensor product `A ⊗ B`. -/
private abbrev tensorUnit (A B : X.Modules) :=
  (tensorAdj X).unit.app (PresheafOfModules.tensorObj (O := X.presheaf) A.val B.val)

private theorem sheafTensor_hom_ext {A B M : X.Modules}
    {f g : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
      X.toRingedSpace.IsSheaf⟩).obj A).obj B ⟶ M}
    (h : ∀ (W : X.Opensᵒᵖ) (a : A.val.obj W) (b : B.val.obj W),
      PresheafOfModules.Hom.app f.val W (PresheafOfModules.Hom.app (tensorUnit A B) W (a ⊗ₜ b)) =
      PresheafOfModules.Hom.app g.val W (PresheafOfModules.Hom.app (tensorUnit A B) W (a ⊗ₜ b))) :
    f = g := by
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  exact PresheafOfModules.tensorObj_hom_ext h

/-- Multiplication `𝒪_X(D) ⊗ 𝒪_X(D') ⟶ 𝒪_X(D + D')` is natural in `D` along the inclusions
`𝒪_X(D₁) ⟶ 𝒪_X(D₂)` for `D₁ ≤ D₂`. -/
@[reassoc]
theorem map_divisorialSheafInclusion_comp_divisorialSheafTensorMul {D₁ D₂ : Divisor X}
    (h : D₁ ≤ D₂) (D' : Divisor X) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
      X.toRingedSpace.IsSheaf⟩).map (divisorialSheafInclusion h)).app D'.divisorialSheaf ≫
      divisorialSheafTensorMul D₂ D' =
    divisorialSheafTensorMul D₁ D' ≫ divisorialSheafInclusion (add_le_add h le_rfl) := by
  refine sheafTensor_hom_ext fun W a b => ?_
  have hn := PresheafOfModules.hom_congr_apply'
    ((tensorAdj X).unit.naturality
      (PresheafOfModules.tensorHom (O := X.presheaf) (divisorialSheafInclusion h).val
        (𝟙 D'.divisorialSheaf.val))) W (a ⊗ₜ b)
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply, PresheafOfModules.tensorHom_tmul,
    Functor.id_map] at hn
  apply Subtype.ext
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply, ← hn,
    divisorialSheafTensorMul_unit]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    divisorialSheafTensorMul_unit]
  rfl

variable {D D' : Divisor X} in
/-- The identification `𝒪_X(D) ≅ 𝒪_X(D')` for equal divisors, by the two inclusions. -/
private def divisorialSheafIsoOfEq (h : D = D') : D.divisorialSheaf ≅ D'.divisorialSheaf where
  hom := divisorialSheafInclusion h.le
  inv := divisorialSheafInclusion h.ge
  hom_inv_id := by rw [divisorialSheafInclusion_comp, divisorialSheafInclusion_refl]
  inv_hom_id := by rw [divisorialSheafInclusion_comp, divisorialSheafInclusion_refl]

/-- Transport of a short exact sequence along isomorphisms of its terms. -/
private theorem shortExact_of_iso_aux {C : Type*} [Category C] [Abelian C] (S₁ : ShortComplex C)
    (hS : S₁.ShortExact) {A B Cc : C} (e₁ : A ≅ S₁.X₁) (φ₂ : S₁.X₂ ≅ B) (φ₃ : S₁.X₃ ≅ Cc)
    (ι : A ⟶ B) (η : B ⟶ Cc) (hι : S₁.f ≫ φ₂.hom = e₁.inv ≫ ι)
    (key : S₁.g ≫ φ₃.hom = φ₂.hom ≫ η) :
    ∃ hz : ι ≫ η = 0, (ShortComplex.mk ι η hz).ShortExact := by
  have hι' : e₁.hom ≫ S₁.f ≫ φ₂.hom = ι := by rw [hι, Iso.hom_inv_id_assoc]
  subst hι'
  have hz : (e₁.hom ≫ S₁.f ≫ φ₂.hom) ≫ η = 0 := by
    rw [Category.assoc, Category.assoc, ← key, ← Category.assoc S₁.f, S₁.zero]
    simp
  refine ⟨hz, ShortComplex.shortExact_of_iso ?_ hS⟩
  exact ShortComplex.isoMk e₁.symm φ₂ φ₃ (by simp) key.symm

variable (X) in
/-- The ring sheaf over which the closed-subscheme sequence is stated. -/
private abbrev Mods := SheafOfModules (_root_.structureSheafRing X.toRingedSpace)

/-- An `𝒪_X`-module, seen over `structureSheafRing`. -/
private abbrev toMods (M : X.Modules) : Mods X := M

/-- The inclusion `𝒪_X(-D) ⟶ 𝒪_X(0)` of an effective divisor `D`. -/
private abbrev negIncl {D : Divisor X} (hD : 0 ≤ D) :
    toMods (Divisor.divisorialSheaf (-D)) ⟶ toMods (0 : Divisor X).divisorialSheaf :=
  divisorialSheafInclusion (neg_nonpos.2 hD)

/-- The restriction `𝒪_X(0) ≅ 𝒪_X ⟶ i_* 𝒪_Z` to the closed subscheme `Z` cut out by `I`. -/
private abbrev quotMap (I : X.IdealSheafData) :
    toMods (0 : Divisor X).divisorialSheaf ⟶
      (RingedSpaceModuleAdjunction.modulePushforward I.subschemeι.toLRSHom.toShHom).obj
        (SheafOfModules.unit (_root_.structureSheafRing I.subscheme.toRingedSpace)) :=
  (divisorialSheafZeroIso (X := X)).hom ≫ Stacks.IdealSheafSequence.divisorQuotientMap I

/-- An element of `𝒪_{X,E}` of order at least `1` along `E` lies in the maximal ideal. -/
private theorem mem_maximalIdeal_of_ordGE_one {E : MMP.Mori.PrimeDivisor X} {b : E.localRing}
    (hb : E.OrdGE 1 (E.toComponent.hom b)) : b ∈ IsLocalRing.maximalIdeal E.localRing := by
  by_contra hmax
  obtain ⟨u, rfl⟩ : IsUnit b := by simpa using hmax
  have h1 := E.one_le_valuation_toComponent u.ne_zero
  have h2 := E.one_le_valuation_toComponent u⁻¹.ne_zero
  have hmul : E.valuation (E.toComponent.hom (u : E.localRing)) *
      E.valuation (E.toComponent.hom ((u⁻¹ : E.localRingˣ) : E.localRing)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have hv : E.valuation (E.toComponent.hom (u : E.localRing)) = 1 :=
    le_antisymm (by
      calc _ = E.valuation (E.toComponent.hom (u : E.localRing)) * 1 := (mul_one _).symm
        _ ≤ _ := by gcongr
        _ = 1 := hmul) h1
  rcases hb with h0 | hb
  · exact (u.isUnit.map E.toComponent.hom).ne_zero h0
  · rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp] at hb
    omega

open scoped Classical in
/-- A regular function `r` on `U` is a section of `𝒪_X(-D)`, for `D` the reduced divisor whose
components are the prime divisors contained in `Z(I)`, exactly when it vanishes at the generic
point of every such prime divisor lying in `U`. -/
private theorem isDivisorialSection_neg_iff (I : X.IdealSheafData) {D : Divisor X}
    (hD : ∀ E, D E = if (E.support : Set X) ⊆ I.support then 1 else 0) {U : X.Opens}
    (r : Γ(X, U)) :
    Divisor.IsDivisorialSection (-D) U ((toRationalFunctionsPresheaf X).app (Opposite.op U) r) ↔
      ∀ E : MMP.Mori.PrimeDivisor X, (E.support : Set X) ⊆ I.support →
        ∀ h : E.genericPoint ∈ U, X.presheaf.germ U _ h r ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint) := by
  have hc : ∀ E, -DivisorWithCoeffs.coeff (-D) E =
      if (E.support : Set X) ⊆ I.support then 1 else 0 := fun E => by
    simp [DivisorWithCoeffs.coeff_apply, hD E]
  constructor
  · intro hs E hE h
    have hne : (E.support ∩ U).Nonempty := ⟨E.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl, h⟩
    have := hs E hne
    rw [hc, if_pos hE] at this
    apply mem_maximalIdeal_of_ordGE_one
    have hgerm := (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h
      E.specializes_genericPoint r)
    erw [toRationalFunctionsPresheaf_app_apply, ← hgerm] at this
    exact this
  · intro hr E hE
    rw [hc]
    split_ifs with hEI
    · have h := E.genericPoint_mem_of_nonempty hE
      have hgerm := (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h
        E.specializes_genericPoint r)
      erw [toRationalFunctionsPresheaf_app_apply, ← hgerm]
      exact MMP.Mori.PrimeDivisor.ordGE_one_toComponent E (hr E hEI h)
    · have := isDivisorialSection_algebraMap (le_refl (0 : Divisor X)) r E hE
      rw [DivisorWithCoeffs.coeff_apply] at this
      simp only [Finsupp.coe_zero, Pi.zero_apply, neg_zero] at this
      exact this

/-- On a reduced closed subscheme `Z(I)` every point of which lies on a prime divisor contained in
`Z(I)`, a regular function on `U` restricts to zero exactly when it vanishes at the generic point
of every such prime divisor lying in `U`. -/
private theorem divisorQuotientMap_app_eq_zero_iff (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hI : ∀ x ∈ I.support, ∃ E : MMP.Mori.PrimeDivisor X,
      (E.support : Set X) ⊆ I.support ∧ x ∈ E.support) (U : X.Opens) (r : Γ(X, U)) :
    (Stacks.IdealSheafSequence.divisorQuotientMap I).val.app (Opposite.op U) r = 0 ↔
      ∀ E : MMP.Mori.PrimeDivisor X, (E.support : Set X) ⊆ I.support →
        ∀ h : E.genericPoint ∈ U, X.presheaf.germ U _ h r ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint) := by
  change I.subschemeι.app U r = 0 ↔ _
  rw [← AlgebraicGeometry.basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
  have hrange := I.range_subschemeι
  constructor
  · intro hbot E hE h hmem
    obtain ⟨d, hd⟩ : E.genericPoint ∈ Set.range I.subschemeι := by
      rw [hrange]
      refine hE ?_
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have hd' : d ∈ I.subschemeι ⁻¹ᵁ X.basicOpen r := by
      change I.subschemeι d ∈ X.basicOpen r
      rwa [hd, Scheme.mem_basicOpen X r _ h]
    rwa [hbot] at hd'
  · intro hgen
    refine eq_bot_iff.2 fun d hd => ?_
    change I.subschemeι d ∈ X.basicOpen r at hd
    obtain ⟨E, hEI, hdE⟩ := hI _ (hrange ▸ Set.mem_range_self d)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hdE
    have hηB : E.genericPoint ∈ X.basicOpen r :=
      (specializes_iff_mem_closure.2 hdE).mem_open (X.basicOpen r).isOpen hd
    have hηU : E.genericPoint ∈ U := X.basicOpen_le r hηB
    exact absurd ((Scheme.mem_basicOpen X r _ hηU).1 hηB)
      ((IsLocalRing.mem_maximalIdeal _).1 (hgen E hEI hηU))

open scoped Classical in
/-- A section of `𝒪_X(0)` restricts to zero on `Z(I)` exactly when it is a section of `𝒪_X(-D)`,
for `D` the reduced divisor of the prime divisors contained in `Z(I)`. -/
private theorem quotMap_app_eq_zero_iff (I : X.IdealSheafData) [IsReduced I.subscheme]
    {D : Divisor X} (hD : ∀ E, D E = if (E.support : Set X) ⊆ I.support then 1 else 0)
    (hI : ∀ x ∈ I.support, ∃ E : MMP.Mori.PrimeDivisor X,
      (E.support : Set X) ⊆ I.support ∧ x ∈ E.support) (U : X.Opens)
    (φ : (0 : Divisor X).divisorialSubmodule U) :
    (quotMap I).val.app (Opposite.op U) φ = 0 ↔ Divisor.IsDivisorialSection (-D) U φ.1 := by
  set r : Γ(X, U) := (divisorialSheafZeroIso (X := X)).hom.app U φ with hr
  have hφ : φ = (structureSheafToDivisorialSheaf (le_refl (0 : Divisor X))).app U r :=
    (congrArg (fun g => g.app U φ) (divisorialSheafZeroIso (X := X)).hom_inv_id).symm
  have hφ1 : φ.1 = (toRationalFunctionsPresheaf X).app (Opposite.op U) r := by
    rw [← coe_structureSheafToDivisorialSheaf_app (le_refl (0 : Divisor X)) U r, ← hφ]
  rw [hφ1, isDivisorialSection_neg_iff I hD, ← divisorQuotientMap_app_eq_zero_iff I hI]
  rfl

open scoped Classical in
/-- **The ideal sequence of a reduced closed subscheme**, read in divisorial sheaves: for `Z(I)`
reduced and covered by the prime divisors it contains, and `D` the reduced divisor of those, the
inclusion `𝒪_X(-D) ⟶ 𝒪_X(0)` followed by `𝒪_X(0) ≅ 𝒪_X ⟶ i_* 𝒪_{Z(I)}` is short exact. -/
private theorem shortExact_negIncl_quotMap (I : X.IdealSheafData) [IsReduced I.subscheme]
    {D : Divisor X} (hD : ∀ E, D E = if (E.support : Set X) ⊆ I.support then 1 else 0)
    (hI : ∀ x ∈ I.support, ∃ E : MMP.Mori.PrimeDivisor X,
      (E.support : Set X) ⊆ I.support ∧ x ∈ E.support) (hD0 : 0 ≤ D) :
    ∃ hz : negIncl hD0 ≫ quotMap I = 0, (ShortComplex.mk _ _ hz).ShortExact := by
  have hz : negIncl hD0 ≫ quotMap I = 0 := by
    refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext φ
    exact (quotMap_app_eq_zero_iff I hD hI U ⟨φ.1, φ.2.mono (neg_nonpos.2 hD0)⟩).2 φ.2
  refine ⟨hz, ?_⟩
  haveI : Mono (negIncl hD0) := inferInstanceAs (Mono (divisorialSheafInclusion _))
  haveI : Epi (quotMap I) := epi_comp'
    (@IsIso.epi_of_iso _ _ _ _ _ ⟨⟨(divisorialSheafZeroIso (X := X)).inv,
      (divisorialSheafZeroIso (X := X)).hom_inv_id, (divisorialSheafZeroIso (X := X)).inv_hom_id⟩⟩)
    (Stacks.IdealSheafSequence.epi_divisorQuotientMap I)
  refine ⟨ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι' _ hz fun {A} k hk => ?_)⟩
  have hmem : ∀ (U : X.Opensᵒᵖ) (a : A.val.obj U), Divisor.IsDivisorialSection (-D) U.unop
      ((k.val.app U a : (0 : Divisor X).divisorialSubmodule U.unop)).1 := fun U a =>
    (quotMap_app_eq_zero_iff I hD hI U.unop _).1 (congrArg (fun g => g.val.app U a) hk)
  refine ⟨⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun a := (⟨(k.val.app U a : (0 : Divisor X).divisorialSubmodule U.unop).1,
            hmem U a⟩ : Divisor.divisorialSubmodule (-D) U.unop)
          map_zero' := Subtype.ext (congrArg
            (fun x : (0 : Divisor X).divisorialSubmodule U.unop => x.1)
            (map_zero (k.val.app U).hom))
          map_add' a b := Subtype.ext (congrArg
            (fun x : (0 : Divisor X).divisorialSubmodule U.unop => x.1)
            (map_add (k.val.app U).hom a b)) }
      naturality U V i := by
        ext a
        exact Subtype.ext <| congrArg (fun x : (0 : Divisor X).divisorialSubmodule V.unop => x.1)
          (PresheafOfModules.naturality_apply k.val i a) }
    fun U r a => Subtype.ext (congrArg (fun x : (0 : Divisor X).divisorialSubmodule U.unop => x.1)
        ((k.val.app U).hom.map_smul r a))⟩, ?_⟩
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext a
  rfl

open scoped Classical in
open Stacks.ProjectionFormula Stacks.RingedSpace RingedSpaceModuleAdjunction in
/-- **The restriction sequence of a reduced divisor.** On a smooth variety `Y` over `k`, let
`Z = Z(I)` be a reduced closed subscheme every point of which lies on a prime divisor contained
in `Z`, and `D` the reduced divisor whose components are the prime divisors contained in `Z`.
For a Cartier divisor `N`, the inclusion `𝒪_Y(N) ⟶ 𝒪_Y(N + D)` and the restriction
`𝒪_Y(N + D) ⟶ i_* i^* 𝒪_Y(N + D)` (the unit of `i^* ⊣ i_*`, `i : Z ⟶ Y`) form a short exact
sequence `0 ⟶ 𝒪_Y(N) ⟶ 𝒪_Y(N + D) ⟶ 𝒪_Y(N + D)|_Z ⟶ 0`. -/
public theorem IsCartier.shortExact_divisorialSheafInclusion_restriction_of_isReduced
    {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : IsVariety k f) (hsm : IsSmoothScheme f) (I : Y.IdealSheafData)
    [IsReduced I.subscheme] (D : Divisor Y)
    (hD : ∀ E, D E = if (E.support : Set Y) ⊆ I.support then 1 else 0)
    (hI : ∀ x ∈ I.support, ∃ E : PrimeDivisor Y, (E.support : Set Y) ⊆ I.support ∧ x ∈ E.support)
    {N : Divisor Y} (hN : N.IsCartier) :
    ∃ hz : divisorialSheafInclusion (le_add_of_nonneg_right
          (Finsupp.le_def.2 fun E => by rw [hD E]; split_ifs <;> simp) : N ≤ N + D) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app
          (N + D).divisorialSheaf = 0,
      (ShortComplex.mk _ _ hz).ShortExact := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have hD0 : 0 ≤ D := Finsupp.le_def.2 fun E => by rw [hD E]; split_ifs <;> simp
  have hF : D.IsCartier := by
    have hD1 : D = ∑ E ∈ D.support, Finsupp.single E 1 := by
      refine (Finsupp.sum_single D).symm.trans (Finset.sum_congr rfl fun E hE => ?_)
      have hEI : (E.support : Set Y) ⊆ I.support := by
        by_contra h; exact Finsupp.mem_support_iff.1 hE (by rw [hD E, if_neg h])
      rw [hD E, if_pos hEI]
    rw [hD1]
    exact Finset.sum_induction _ _ (fun _ _ => IsCartier.add) isCartier_zero fun E _ =>
      MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm E
  have hL : (N + D).IsCartier := hN.add hF
  set L := (N + D).divisorialSheaf
  have hinv := hL.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L := hinv
  haveI hinv' : Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      (structureRingSheaf Y.toRingedSpace).property L := hinv
  let Fu : SheafOfModules (structureSheafRing Y.toRingedSpace) ⥤
      SheafOfModules (structureSheafRing Y.toRingedSpace) :=
    (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩).flip.obj L
  have : Fu.IsEquivalence :=
    (Stacks.SheafOfModules.Invertible.isInvertible_iff_tensorRightFunctor_isEquivalence
      Y.presheaf Y.ringCatSheaf.2 L).1 ‹_›
  have : Fu.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full Fu
  obtain ⟨hz0, hS0⟩ := shortExact_negIncl_quotMap I hD hI hD0
  have hS1 := hS0.map_of_exact Fu
  -- the multiplication isomorphisms
  haveI := (hF.neg).isIso_divisorialSheafTensorMul hL
  haveI := (isCartier_zero (X := Y)).isIso_divisorialSheafTensorMul hL
  let m₁ := asIso (divisorialSheafTensorMul (-D) (N + D))
  let m₀ := asIso (divisorialSheafTensorMul 0 (N + D))
  let φ₂ : Fu.obj (divisorialSheaf 0) ≅ L := m₀ ≪≫ divisorialSheafIsoOfEq (zero_add _)
  let ε : Fu.obj (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) ≅ L :=
    Fu.mapIso (divisorialSheafZeroIso (X := Y)).symm ≪≫ φ₂
  let i := I.subschemeι.toLRSHom.toShHom
  have hiso := isIso_projectionFormulaMap i
    (SheafOfModules.unit (structureRingSheaf I.subscheme.toRingedSpace)) L
  have hcomp := tensorUnitToPushforward_comp_projectionFormulaMap' (f := i) L
  have hsc := isIso_structureComparison i L
  let ψi : ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨I.subscheme.toRingedSpace.presheaf,
              I.subscheme.toRingedSpace.IsSheaf⟩))).obj
        (SheafOfModules.unit (structureRingSheaf I.subscheme.toRingedSpace),
          (pullbackFunctor i).obj L) ≅ (pullbackFunctor i).obj L :=
    (@asIso _ _ _ _ _ hsc).symm ≪≫ (pullbackFunctor i).mapIso ε
  let φ₃ := (@asIso _ _ _ _ _ hiso) ≪≫ (pushforwardFunctor i).mapIso ψi
  have key : Fu.map (Stacks.IdealSheafSequence.divisorQuotientMap I) ≫ φ₃.hom =
      ε.hom ≫ (pullbackAdjunction i).unit.app L := by
    have h1 : Fu.map (Stacks.IdealSheafSequence.divisorQuotientMap I) ≫
        projectionFormulaMap' i
          (SheafOfModules.unit (structureRingSheaf I.subscheme.toRingedSpace)) L =
        (pullbackAdjunction i).unit.app
          (((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩))).obj
            (SheafOfModules.unit (structureRingSheaf Y.toRingedSpace), L)) ≫
        (pushforwardFunctor i).map (structureComparison i L) := by
      rw [← hcomp]
      simp only [Fu, unitHom_eq, Functor.uncurry_obj_map, Prod.mkHom]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
      rfl
    have h2 := (pullbackAdjunction i).unit.naturality ε.hom
    have hφ : φ₃.hom = projectionFormulaMap' i
        (SheafOfModules.unit (structureRingSheaf I.subscheme.toRingedSpace)) L ≫
        (pushforwardFunctor i).map ((@asIso _ _ _ _ _ hsc).inv ≫
          (pullbackFunctor i).map ε.hom) := rfl
    rw [hφ]
    erw [← Category.assoc, h1, Category.assoc, ← CategoryTheory.Functor.map_comp]
    erw [asIso_inv, IsIso.hom_inv_id_assoc]
    exact h2.symm
  refine shortExact_of_iso_aux _ hS1
    (divisorialSheafIsoOfEq (show N = -D + (N + D) by abel) ≪≫ m₁.symm) φ₂ φ₃ _ _ ?_ ?_
  · change ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.toRingedSpace.presheaf,
        Y.toRingedSpace.IsSheaf⟩).map (divisorialSheafInclusion
          (neg_nonpos.2 hD0 : -D ≤ 0))).app
          (N + D).divisorialSheaf ≫
        divisorialSheafTensorMul 0 (N + D) ≫ divisorialSheafInclusion (zero_add (N + D)).le =
        (divisorialSheafTensorMul (-D) (N + D) ≫
          divisorialSheafInclusion (show N = -D + (N + D) by abel).ge) ≫
        divisorialSheafInclusion (le_add_of_nonneg_right hD0 : N ≤ N + D)
    refine (Category.assoc _ _ _).symm.trans
      ((map_divisorialSheafInclusion_comp_divisorialSheafTensorMul _ _ =≫ _).trans ?_)
    exact (Category.assoc _ _ _).trans ((_ ≫= divisorialSheafInclusion_comp _ _).trans
      ((_ ≫= (divisorialSheafInclusion_comp _ _).symm).trans (Category.assoc _ _ _).symm))
  · change Fu.map ((divisorialSheafZeroIso (X := Y)).hom ≫
      Stacks.IdealSheafSequence.divisorQuotientMap I) ≫ φ₃.hom = φ₂.hom ≫ _
    refine (Fu.map_comp _ _ =≫ _).trans ((Category.assoc _ _ _).trans ((Fu.map _ ≫= key).trans ?_))
    exact (Category.assoc _ _ _).symm.trans (((Category.assoc _ _ _).symm.trans
      (((Fu.mapIso (divisorialSheafZeroIso (X := Y))).hom_inv_id =≫ φ₂.hom).trans
        (Category.id_comp _))) =≫ _)

end

/-- **The restriction sequence of a prime divisor.** On a smooth variety `Y` over `k`, for a
prime divisor `F` with closed immersion `i` and a Cartier divisor `N`, the inclusion
`𝒪_Y(N) ⟶ 𝒪_Y(N + F)` and the restriction `𝒪_Y(N + F) ⟶ i_* i^* 𝒪_Y(N + F)` (the unit of
`i^* ⊣ i_*`) form a short exact sequence `0 ⟶ 𝒪_Y(N) ⟶ 𝒪_Y(N + F) ⟶ 𝒪_Y(N + F)|_F ⟶ 0`.
This is the case `I = F.idealSheaf`, `D = F` of
`IsCartier.shortExact_divisorialSheafInclusion_restriction_of_isReduced`. -/
@[mmp "lem_mmp_foundation_km_divisor_restriction_sequence"]
public theorem IsCartier.shortExact_divisorialSheafInclusion_restriction {k : Type u} [Field k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : IsVariety k f) (hsm : IsSmoothScheme f) (F : PrimeDivisor Y) {N : Divisor Y}
    (hN : N.IsCartier) :
    ∃ hz : divisorialSheafInclusion
          (le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one) :
            N ≤ N + Finsupp.single F 1) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction F.idealSheaf.subschemeι).unit.app
          (N + Finsupp.single F 1).divisorialSheaf = 0,
      (ShortComplex.mk _ _ hz).ShortExact := by
  haveI := F.integral
  refine shortExact_divisorialSheafInclusion_restriction_of_isReduced f hY hsm F.idealSheaf _
    (fun E => ?_) (fun x hx => ⟨F, subset_rfl, hx⟩) hN
  classical
  by_cases hE : E = F
  · subst hE; simp
  · rw [Finsupp.single_apply, if_neg (Ne.symm hE), if_neg fun h => hE
      (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support F E (h (by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl))).symm]

end MMP.Mori.Divisor

end

section

open IsLocalRing

namespace MMP.Foundation

/-- An element of `I ^ k` lies in `I • (I ^ k)` exactly when it lies in `I ^ (k + 1)`. -/
private theorem mem_smul_top_iff_mem_pow_succ {A : Type*} [CommRing A] (I : Ideal A) (k : ℕ)
    (y : ↥(I ^ k)) : y ∈ (I • ⊤ : Submodule A ↥(I ^ k)) ↔ (y : A) ∈ I ^ (k + 1) := by
  rw [Submodule.mem_smul_top_iff, Ideal.smul_eq_mul, ← pow_succ']

section Basis

/-- An exponent in the support of a homogeneous polynomial of degree `k` has total degree `k`. -/
private theorem sum_eq_of_mem_support {A : Type*} [CommRing A] {c k : ℕ}
    {P : MvPolynomial (Fin c) A} (hP : P.IsHomogeneous k) {e : Fin c →₀ ℕ} (he : e ∈ P.support) :
    ∑ i, e i = k := by
  have := hP (MvPolynomial.mem_support_iff.1 he)
  rw [Finsupp.weight_apply] at this
  simpa [Finsupp.sum_fintype] using this

variable {A : Type*} [CommRing A] (I : Ideal A) {c : ℕ} (x : Fin c → A) (k : ℕ)

/-- The monomial `x ^ e` lies in `I ^ k` when `|e| = k` and every `x i` lies in `I`. -/
private theorem prod_pow_mem_pow (hx : ∀ i, x i ∈ I) (e : Fin c →₀ ℕ)
    (he : e ∈ (Finset.univ : Finset (Fin c)).finsuppAntidiag k) :
    ∏ i, x i ^ e i ∈ I ^ k := by
  have hk : ∑ i, e i = k := (Finset.mem_finsuppAntidiag.1 he).1
  rw [← hk]
  exact AssociatedGraded.prod_mem_pow_sum I e (fun i => x i ^ e i)
    (fun i => Ideal.pow_mem_pow (hx i) _) Finset.univ

/-- The class in `I ^ k / I ^ (k + 1)` of the monomial `x ^ e`, `|e| = k`. -/
private noncomputable def monomialClass (hx : ∀ i, x i ∈ I)
    (e : (Finset.univ : Finset (Fin c)).finsuppAntidiag k) :
    ↥(I ^ k) ⧸ (I • ⊤ : Submodule A ↥(I ^ k)) :=
  Submodule.Quotient.mk ⟨∏ i, x i ^ e.1 i, prod_pow_mem_pow I x k hx e.1 e.2⟩

private theorem span_monomialClass (hx : ∀ i, x i ∈ I) (hI : Ideal.span (Set.range x) = I) :
    ⊤ ≤ Submodule.span (A ⧸ I) (Set.range (monomialClass I x k hx)) := by
  classical
  rintro q -
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
  obtain ⟨P, hP, hPz⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous x (z : A)).1
    (by rw [hI]; exact z.2)
  have hmem : ∀ e ∈ P.support, e ∈ (Finset.univ : Finset (Fin c)).finsuppAntidiag k :=
    fun e he => Finset.mem_finsuppAntidiag.2
      ⟨sum_eq_of_mem_support hP he, by simp⟩
  have hz : z = ∑ e ∈ P.support.attach, P.coeff e.1 •
      (⟨∏ i, x i ^ e.1 i, prod_pow_mem_pow I x k hx e.1 (hmem e.1 e.2)⟩ : ↥(I ^ k)) := by
    apply Subtype.ext
    rw [← hPz, MvPolynomial.eval_eq']
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, smul_eq_mul]
    exact (Finset.sum_attach P.support fun e => P.coeff e * ∏ i, x i ^ e i).symm
  rw [hz, ← Submodule.mkQ_apply, map_sum]
  refine Submodule.sum_mem _ fun e _ => ?_
  rw [map_smul, Submodule.mkQ_apply]
  change Ideal.Quotient.mk I (P.coeff e.1) • monomialClass I x k hx ⟨e.1, hmem e.1 e.2⟩ ∈ _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

private theorem linearIndependent_monomialClass (hx : ∀ i, x i ∈ I)
    (hinj : Function.Injective (AssociatedGraded.polyGradedHom I x hx)) :
    LinearIndependent (A ⧸ I) (monomialClass I x k hx) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg e₀
  choose a ha using fun e => Ideal.Quotient.mk_surjective (I := I) (g e)
  set P : MvPolynomial (Fin c) A := ∑ e, MvPolynomial.monomial e.1 (a e) with hPdef
  have hP : P.IsHomogeneous k := MvPolynomial.IsHomogeneous.sum _ _ _ fun e _ =>
    MvPolynomial.isHomogeneous_monomial _ (by
      rw [Finsupp.degree_eq_sum]
      exact (Finset.mem_finsuppAntidiag.1 e.2).1)
  have hcoeff : P.coeff e₀.1 = a e₀ := by
    rw [hPdef, MvPolynomial.coeff_sum, Finset.sum_eq_single e₀]
    · simp
    · intro b _ hb
      rw [MvPolynomial.coeff_monomial, if_neg]
      exact fun h => hb (Subtype.ext h)
    · simp
  have hev : MvPolynomial.eval x P ∈ I ^ (k + 1) := by
    have h0 : (⟨MvPolynomial.eval x P,
        AssociatedGraded.eval_mem_pow_of_isHomogeneous I x hx hP⟩ : ↥(I ^ k)) =
        ∑ e, a e • (⟨∏ i, x i ^ e.1 i, prod_pow_mem_pow I x k hx e.1 e.2⟩ : ↥(I ^ k)) := by
      apply Subtype.ext
      change MvPolynomial.eval x P = _
      rw [hPdef, map_sum, AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ fun i => pow_zero _]
      rfl
    rw [← mem_smul_top_iff_mem_pow_succ I k ⟨_,
      AssociatedGraded.eval_mem_pow_of_isHomogeneous I x hx hP⟩,
      ← Submodule.Quotient.mk_eq_zero, h0, ← hg, ← Submodule.mkQ_apply, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← ha e, Submodule.mkQ_apply, monomialClass, Module.Quotient.mk_smul_mk]
  have h0 : AssociatedGraded.polyGradedHom I x hx (P.map (Ideal.Quotient.mk I)) =
      AssociatedGraded.polyGradedHom I x hx 0 := by
    rw [AssociatedGraded.polyGradedHom_map I x hx hP, map_zero]
    exact (MMP.Flips.associatedGraded_classOfPow_eq_zero_iff I k _).2 hev
  have h2 := congrArg (·.coeff e₀.1) (hinj h0)
  rw [MvPolynomial.coeff_map, hcoeff, MvPolynomial.coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
    ha] at h2
  exact h2

/-- **The dimension count.** If `x_1, …, x_c` generate `I` and the canonical map
`(A ⧸ I)[X_1, …, X_c] → ⨁ I ^ k / I ^ (k + 1)` is injective, then the classes of the monomials of
degree `k` form an `A ⧸ I`-basis of `I ^ k / I ^ (k + 1)`, which therefore has dimension
`(c + k - 1).choose k`. -/
private theorem finrank_pow_quotient_smul_top [Nontrivial (A ⧸ I)] (hx : ∀ i, x i ∈ I)
    (hI : Ideal.span (Set.range x) = I)
    (hinj : Function.Injective (AssociatedGraded.polyGradedHom I x hx)) :
    Module.finrank (A ⧸ I) (↥(I ^ k) ⧸ (I • ⊤ : Submodule A ↥(I ^ k))) =
      (c + k - 1).choose k := by
  rw [Module.finrank_eq_card_basis (Module.Basis.mk (linearIndependent_monomialClass I x k hx hinj)
    (span_monomialClass I x k hx hI)), Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_univ, Fintype.card_fin]

end Basis

/-- In a regular local ring `R` of Krull dimension `n ≥ 1` with maximal ideal `𝔪`, the
`R ⧸ 𝔪`-vector space `𝔪 ^ k / 𝔪 ^ (k + 1)` has dimension `(k + n - 1).choose (n - 1)`. -/
@[mmp "lem_mmp_foundation_km_regular_graded_dimension"]
public theorem finrank_pow_maximalIdeal_quotient_smul_top {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {n : ℕ} (hn : 1 ≤ n) (hdim : ringKrullDim R = n) (k : ℕ) :
    Module.finrank (R ⧸ maximalIdeal R)
        (↥(maximalIdeal R ^ k) ⧸ (maximalIdeal R • ⊤ : Submodule R ↥(maximalIdeal R ^ k))) =
      (k + n - 1).choose (n - 1) := by
  obtain ⟨s, hcard, hspan⟩ :=
    (IsNoetherian.noetherian (maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  have hxs : Ideal.ofList s.toList = maximalIdeal R := by
    rw [← hspan]; exact congrArg Ideal.span (by ext x; simp)
  have hmin : s.toList.length = (maximalIdeal R).spanFinrank := by simp [hcard]
  have hx : ∀ i : Fin s.toList.length, s.toList[i] ∈ maximalIdeal R := fun i => by
    rw [← hxs]; exact Ideal.subset_span (List.getElem_mem _)
  have hlen : s.toList.length = n := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hdim, ← hmin] at h
    exact_mod_cast h
  rw [finrank_pow_quotient_smul_top (maximalIdeal R) _ k hx
    ((Stacks.QuasiregularSequence.ofList_eq_span_range s.toList).symm.trans hxs)
    (IsRegularLocalRing.gradedRing_maximalIdeal_isPolynomialAlgebra s.toList hxs hmin hx).1.1, hlen]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 + k - 1 = k + m by omega, show k + (m + 1) - 1 = k + m by omega,
    Nat.add_sub_cancel, Nat.choose_symm_add]

end MMP.Foundation

end

end
