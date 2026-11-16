/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
public import MMP.AlgebraicGeometry.RegularEmbedding.ConesBlowups
public import StacksFrontier.AlgebraicGeometry.Blowup.SecondCentreChartCover
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.SituationData
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksFrontier.RingTheory.MvPolynomial.VariablesRegular
public import StacksFrontier.RingTheory.Koszul.Blowup
public import StacksFrontier.RingTheory.Koszul.H1RegularRingEquiv
public import StacksFrontier.RingTheory.AffineBlowup.ModelComparison
public import StacksFrontier.RingTheory.AffineBlowup.ChartEquiv
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.RingTheory.RegularLocalRing.MaximalCohenMacaulay
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square

/-!
# Charts of blow-ups and orders under flat pullback

Let `π : B_IX ⟶ X` be the blow-up of a scheme `X` along a quasi-coherent ideal sheaf `I`, and
let `x_1, …, x_r ∈ 𝒪_X(U)` generate `I|_U` on an open `U`. Over every affine open `V ⊆ U` the
blow-up is `Proj ⨁_d I(V)^d`, generated over degree zero by the degree-one sections `x_i t`; a
homogeneous prime containing all of them contains the irrelevant ideal, so the charts
`U_i = D_+(x_i)` cover `π⁻¹(U)`. Over an affine `U` the chart `U_ℓ` is the standard affine chart
`Spec 𝒪_X(U)[I(U)/x_ℓ]`. When the `x_i` are the first `r` members of a system of local
coordinates on `U`, its ring is `𝒪_X(U)[T_i : i ≠ ℓ]/(x_i - T_i x_ℓ)` with `T_i = x_i/x_ℓ`.

The file also states that orders of ideals are unchanged under a flat morphism of regular
schemes with regular closed fibres. Closed projective cones of graded quotients are in
`MMP.Foundations.Flips.ResolutionInputs.ProjectiveConeQuotient`.

## Main definitions

* `MMP.Flips.ResolutionInputs.chartFraction`: the section `x_i / x_ℓ` of `𝒪(U_ℓ)`.
* `MMP.Flips.ResolutionInputs.chartPresentation`: `𝒪_X(U)[T_i : i ≠ ℓ] → 𝒪(U_ℓ)`,
  `T_i ↦ x_i / x_ℓ`.

## Main results

* `MMP.Flips.ResolutionInputs.iSup_chart_eq_preimage`: the charts `U_1, …, U_r` cover `π⁻¹(U)`.
* `MMP.Flips.ResolutionInputs.chart_eq_blowUpChartOpen`,
  `MMP.Flips.ResolutionInputs.isAffineOpen_chart`: over an affine `U` the chart `U_ℓ` is the
  standard affine chart.
* `MMP.Flips.ResolutionInputs.chartPresentation_surjective_and_ker`: the equations of a
  coordinate-centre chart.
* `MMP.Flips.ResolutionInputs.multAt_comap_eq`: `ord_y(φ^*I) = ord_{φ(y)} I`.

## Implementation notes

The chart `U_ℓ` over an arbitrary open `U` is `MMP.Resolution.BlowupChartData.chart`, the union
of the standard charts over the affine opens inside `U`. In the coordinate-chart statement the
smoothness of `X` is not assumed: the étale coordinate map on `U` is all that is used.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.47, 3.60]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing Opposite

universe u

namespace MMP.Flips.ResolutionInputs

open MMP.Resolution

/-! ### Blowup relations of an `H₁`-regular sequence -/

section BlowupRelations

open MvPolynomial

private theorem isWeaklyRegular_ofFn_X_comp {R : Type*} [CommRing R] {τ : Type*} {m : ℕ}
    (σ : Fin m → τ) (hσ : Function.Injective σ) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial τ R)
      (List.ofFn fun j => (X (σ j) : MvPolynomial τ R)) := by
  rw [RingTheory.Sequence.isWeaklyRegular_iff]
  intro i hi
  have hin : i < m := by simpa using hi
  have hset : Ideal.ofList ((List.ofFn fun j => (X (σ j) : MvPolynomial τ R)).take i) =
      Ideal.span (X '' (σ '' {j : Fin m | (j : ℕ) < i})) := by
    rw [← Fin.ofFn_take_eq_take_ofFn hin.le]
    have hs : {r : MvPolynomial τ R | r ∈ List.ofFn (Fin.take i hin.le fun j => X (σ j))}
        = X '' (σ '' {j : Fin m | (j : ℕ) < i}) := by
      refine Set.ext fun r => ?_
      constructor
      · intro hr
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
        exact ⟨σ (Fin.castLE hin.le j), ⟨_, by simp, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, by simp [Fin.take, Fin.castLE]⟩
    exact congrArg Ideal.span hs
  rw [MvPolynomial.ideal_smul_top, hset, isSMulRegular_iff_right_eq_zero_of_smul]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, List.getElem_ofFn,
    smul_eq_mul] at hx
  refine (Submodule.Quotient.mk_eq_zero _).2 (mem_span_X_image_of_X_mul_mem ?_ hx)
  rintro ⟨j, hj, hji⟩
  obtain rfl := hσ hji
  simp at hj

private theorem isH1Regular_X_comp {R : Type*} [CommRing R] {τ : Type*} {m : ℕ}
    (σ : Fin m → τ) (hσ : Function.Injective σ) :
    Koszul.IsH1Regular fun j => (X (σ j) : MvPolynomial τ R) :=
  (Koszul.isH1RegularOn_self_iff _).1
    (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular.1
      (isWeaklyRegular_ofFn_X_comp σ hσ)).isH1RegularOn

/-- For an `H₁`-regular sequence `g_0, …, g_n`, the head `g_0` is a nonzerodivisor modulo the
tail. -/
theorem head_isSMulRegular_quotient_tail_of_isH1Regular {A : Type*} [CommRing A] {n : ℕ}
    (g : Fin (n + 1) → A) (hg : Koszul.IsH1Regular g) :
    IsSMulRegular (A ⧸ Ideal.span (Set.range fun i : Fin n => g i.succ)) (g 0) := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro x hx
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hx
  let z : Fin (n + 1) → A := Fin.cases x (fun i => -c i)
  have hz : ∑ i, z i * g i = 0 := by
    rw [Fin.sum_univ_succ]
    simp only [z, Fin.cases_zero, Fin.cases_succ]
    rw [smul_eq_mul] at hc
    simp_rw [neg_mul]
    rw [Finset.sum_neg_distrib, hc]
    ring
  have hcoord : ∀ w ∈ Koszul.relSpan g,
      w 0 ∈ Ideal.span (Set.range fun i : Fin n => g i.succ) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨ij, rfl⟩ := hw
      change Koszul.trivRel g ij.1 ij.2 0 ∈ _
      rcases Fin.eq_zero_or_eq_succ ij.1 with hi | ⟨i, hi⟩ <;>
        rcases Fin.eq_zero_or_eq_succ ij.2 with hj | ⟨j, hj⟩
      all_goals rw [hi, hj]
      · simp [Koszul.trivRel]
      · simpa [Koszul.trivRel] using
          neg_mem (Ideal.subset_span (s := Set.range fun i : Fin n => g i.succ) ⟨j, rfl⟩)
      · simpa [Koszul.trivRel] using Ideal.subset_span (s := Set.range fun i : Fin n => g i.succ)
          ⟨i, rfl⟩
      · simp [Koszul.trivRel]
    | zero => simp
    | add a b _ _ ha hb => exact Ideal.add_mem _ ha hb
    | smul a w _ hw => simpa [smul_eq_mul] using Ideal.mul_mem_left _ a hw
  simpa [z] using hcoord z ((Koszul.isH1Regular_iff_forall g).1 hg z hz)

/-- If `a, b_{e 0}, …` is `H₁`-regular, then `C a` is a nonzerodivisor modulo the blowup
relations `C (b i) - X i * C a`. -/
theorem mem_span_relations_of_C_pow_mul_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ}
    (e : Fin n ≃ ι) (a : R) (b : ι → R)
    (hf : Koszul.IsH1Regular (Fin.cases a (fun j => b (e j)) : Fin (n + 1) → R))
    {p : MvPolynomial ι R} {k : ℕ}
    (hp : C a ^ k * p ∈ Ideal.span (Set.range fun i : ι => C (b i) - X i * C a)) :
    p ∈ Ideal.span (Set.range fun i : ι => C (b i) - X i * C a) := by
  set f : Fin (n + 1) → R := Fin.cases a (fun j => b (e j))
  have hg := Koszul.isH1Regular_relationSequence f hf
  have hreg := head_isSMulRegular_quotient_tail_of_isH1Regular _ hg
  simp only [Fin.cases_zero, Fin.cases_succ, f] at hreg
  set Jf : Ideal (MvPolynomial (Fin n) R) :=
    Ideal.span (Set.range fun i : Fin n => C a * X i - C (b (e i))) with hJf
  let ren := MvPolynomial.renameEquiv R e
  set Jι := Ideal.span (Set.range fun i : ι => C (b i) - X i * C a) with hJι
  have h1 : Jι.map (ren.symm : MvPolynomial ι R →+* MvPolynomial (Fin n) R) ≤ Jf := by
    rw [hJι, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have : (ren.symm : MvPolynomial ι R →+* MvPolynomial (Fin n) R) (C (b i) - X i * C a) =
        -(C a * X (e.symm i) - C (b (e (e.symm i)))) := by
      simp [ren]
      ring
    rw [this]
    exact neg_mem (Ideal.subset_span ⟨_, rfl⟩)
  have h2 : Jf.map (ren : MvPolynomial (Fin n) R →+* MvPolynomial ι R) ≤ Jι := by
    rw [hJf, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    have : (ren : MvPolynomial (Fin n) R →+* MvPolynomial ι R) (C a * X j - C (b (e j))) =
        -(C (b (e j)) - X (e j) * C a) := by
      simp [ren]
      ring
    rw [this]
    exact neg_mem (Ideal.subset_span ⟨_, rfl⟩)
  have hq : ren.symm (C a ^ k * p) ∈ Jf := h1 (Ideal.mem_map_of_mem _ hp)
  rw [map_mul, map_pow, show ren.symm (C a) = C a from ren.symm.commutes a] at hq
  have := mem_of_isSMulRegular_quotient_of_smul_mem (hreg.pow k)
    (by simpa [smul_eq_mul] using hq)
  simpa using h2 (Ideal.mem_map_of_mem _ this)

/-- If `a, b_{e 0}, …, b_{e (n-1)}` is `H₁`-regular, then the `R`-algebra map
`R[X_i : i ∈ ι] → R_a`, `X_i ↦ b_i / a`, hits every element of the affine blow-up algebra
`R[I/a]` for `I = (a, b_i)`, and its kernel is the ideal generated by the `b_i - a X_i`. -/
theorem aeval_mk'_range_and_ker_of_isH1Regular {R : Type*} [CommRing R] {ι : Type*} {n : ℕ}
    (e : Fin n ≃ ι) (a : R) (b : ι → R)
    (hf : Koszul.IsH1Regular (Fin.cases a (fun j => b (e j)) : Fin (n + 1) → R)) :
    (∀ y ∈ affineBlowupAlgebra (Ideal.span (insert a (Set.range b))) a (Localization.Away a),
      ∃ p : MvPolynomial ι R, MvPolynomial.aeval (R := R)
        (fun i => IsLocalization.mk' (Localization.Away a) (b i)
        (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)) p = y) ∧
    RingHom.ker (MvPolynomial.aeval (R := R) (fun i => IsLocalization.mk' (Localization.Away a)
        (b i) (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a))) =
      Ideal.span (Set.range fun i : ι => C (b i) - X i * C a) := by
  set I := Ideal.span (insert a (Set.range b))
  set φ : MvPolynomial ι R →ₐ[R] Localization.Away a := MvPolynomial.aeval (fun i =>
    IsLocalization.mk' (Localization.Away a) (b i)
      (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a))
  have hφ : ∀ i, φ (X i) * algebraMap R (Localization.Away a) a =
      algebraMap R (Localization.Away a) (b i) := by
    intro i
    simp only [φ, MvPolynomial.aeval_X]
    exact IsLocalization.mk'_spec _ _ _
  obtain ⟨hrange, hker⟩ := Ideal.range_eq_affineBlowup_and_ker_eq_saturation rfl φ hφ
  have ha : a ∈ I := Ideal.subset_span (Set.mem_insert _ _)
  refine ⟨fun y hy => ?_, ?_⟩
  · have hmem : y ∈ Stacks.AffineBlowup.affineBlowupAlgebra (R := R) I a ha := by
      rw [Stacks.AffineBlowup.affineBlowupAlgebra_eq_affineBlowupAlgebraAway _ _ ha,
        affineBlowupAlgebraAway_eq_affineBlowupAlgebra]
      exact hy
    rw [Stacks.AffineBlowup.mem_affineBlowupAlgebra ha] at hmem
    change y ∈ Set.range φ
    rw [hrange]
    exact hmem
  · have hJ : Ideal.span (Set.range fun i : ι => C a * X i - C (b i)) =
        Ideal.span (Set.range fun i : ι => C (b i) - X i * C a) := by
      apply le_antisymm <;> refine Ideal.span_le.2 ?_ <;> rintro _ ⟨i, rfl⟩
      · dsimp only
        rw [show C a * X i - C (b i) = -(C (b i) - X i * C a : MvPolynomial ι R) by ring]
        exact neg_mem (Ideal.subset_span ⟨i, rfl⟩)
      · dsimp only
        rw [show C (b i) - X i * C a = -(C a * X i - C (b i) : MvPolynomial ι R) by ring]
        exact neg_mem (Ideal.subset_span ⟨i, rfl⟩)
    ext p
    rw [RingHom.mem_ker]
    change φ p = 0 ↔ _
    rw [hker p, hJ]
    exact ⟨fun ⟨k, hk⟩ => mem_span_relations_of_C_pow_mul_mem e a b hf (k := k)
      (by simpa [MvPolynomial.smul_eq_C_mul] using hk), fun hp => ⟨0, by simpa using hp⟩⟩

end BlowupRelations

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- On affine opens `V ≤ W`, the chart of the blow-up at the restriction of a section `a` of `I`
over `W` is the part of the chart at `a` lying over `V`. -/
theorem blowUpChartOpen_restrict {V W : X.affineOpens} (h : V.1 ≤ W.1) (a : I.ideal W)
    (ha : (X.presheaf.map (homOfLE h).op).hom (a : Γ(X, W.1)) ∈ I.ideal V) :
    (blowUpChartOpen I V ⟨_, ha⟩).1 = (blowUpChartOpen I W a).1 ⊓ blowUpToBase I ⁻¹ᵁ V.1 := by
  ext x
  constructor
  · intro hx
    have hxV : blowUpToBase I x ∈ V.1 := blowUpChartOpen_le I V _ hx
    refine ⟨(mem_blowUpChartOpen_iff I W a x (h hxV)).mpr ?_, hxV⟩
    rw [(mem_blowUpChartOpen_iff I V _ x hxV).mp hx, TopCat.Presheaf.germ_res_apply]
  · rintro ⟨hxW, hxV : blowUpToBase I x ∈ V.1⟩
    refine (mem_blowUpChartOpen_iff I V _ x hxV).mpr ?_
    rw [(mem_blowUpChartOpen_iff I W a x (h hxV)).mp hxW, TopCat.Presheaf.germ_res_apply]

variable {I} (c : BlowupChartData I)

/-- The chart `U_ℓ` of the blow-up over an affine open `U` is the standard chart `D_+(x_ℓ)` of
`π⁻¹(U) = Proj ⨁_d I(U)^d`. -/
theorem chart_eq_blowUpChartOpen (hU : IsAffineOpen c.U) (ℓ : Fin c.r) :
    c.chart ℓ = (blowUpChartOpen I ⟨c.U, hU⟩ ⟨_, c.restrict_mem_ideal ⟨c.U, hU⟩ le_rfl ℓ⟩).1 := by
  refine le_antisymm (iSup₂_le fun V h => ?_) ?_
  · have hres : (X.presheaf.map (homOfLE (show V.1 ≤ (⟨c.U, hU⟩ : X.affineOpens).1 from h)).op).hom
        ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x ℓ)) =
        (X.presheaf.map (homOfLE h).op).hom (c.x ℓ) := by
      rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
      rfl
    have key := blowUpChartOpen_restrict I (V := V) (W := ⟨c.U, hU⟩) h
      ⟨_, c.restrict_mem_ideal ⟨c.U, hU⟩ le_rfl ℓ⟩ (hres ▸ c.restrict_mem_ideal V h ℓ)
    have he : (⟨(X.presheaf.map (homOfLE h).op).hom (c.x ℓ), c.restrict_mem_ideal V h ℓ⟩ :
        I.ideal V) = ⟨_, hres ▸ c.restrict_mem_ideal V h ℓ⟩ := Subtype.ext hres.symm
    rw [he, key]
    exact inf_le_left
  · exact le_iSup₂_of_le (⟨c.U, hU⟩ : X.affineOpens) (le_refl c.U) le_rfl

/-- **The charts over an affine open are affine** (Kollár (3.60.2)). -/
@[mmp "lem_mmp_foundation_coordinate_blowup_chart_ring"]
theorem isAffineOpen_chart (hU : IsAffineOpen c.U) (ℓ : Fin c.r) : IsAffineOpen (c.chart ℓ) := by
  rw [chart_eq_blowUpChartOpen c hU ℓ]
  exact (blowUpChartOpen I _ _).2

/-- **The degree-one generator charts cover a blow-up.** If `x_1, …, x_r ∈ 𝒪_X(U)` generate
`I|_U`, the charts `U_1, …, U_r` cover `π⁻¹(U)`, for an arbitrary open `U`. -/
@[mmp "lem_mmp_foundation_kr_rees_charts_cover"]
theorem iSup_chart_eq_preimage : ⨆ ℓ, c.chart ℓ = blowUpToBase I ⁻¹ᵁ c.U := by
  classical
  refine le_antisymm (iSup_le c.chart_le) fun x hx => ?_
  have hxU : blowUpToBase I x ∈ c.U := hx
  obtain ⟨W, hW, hxV, hWU⟩ := exists_isAffineOpen_mem_and_subset hxU
  let V : X.affineOpens := ⟨W, hW⟩
  have h : V.1 ≤ c.U := hWU
  let g : Fin c.r → I.ideal V := fun ℓ => ⟨_, c.restrict_mem_ideal V h ℓ⟩
  let A : Finset (I.ideal V) := insert 0 (Finset.univ.image g)
  have hspan : Ideal.span ((fun a : I.ideal V => (a : Γ(X, V.1))) '' (A : Set (I.ideal V))) =
      I.ideal V := by
    refine Eq.trans ?_ (c.generates V h).symm
    simp only [A, Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.image_insert_eq, ZeroMemClass.coe_zero, Ideal.span_insert_zero]
    congr 1
    rw [← Set.range_comp]
    rfl
  have hcov := iSup_blowUpChartOpen I V A (Finset.insert_nonempty _ _) hspan
  have hxV' : x ∈ blowUpToBase I ⁻¹ᵁ V.1 := hxV
  rw [← hcov] at hxV'
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hxV'
  obtain ⟨haA, hxa⟩ := TopologicalSpace.Opens.mem_iSup.mp ha
  rcases Finset.mem_insert.mp haA with rfl | haA
  · exfalso
    have hx0 : x ∈ (blowUpAffineChart I V 0).opensRange := by
      rw [← Scheme.Hom.image_top_eq_opensRange]
      exact hxa
    obtain ⟨y, -⟩ := hx0
    exact (isEmpty_spec_blowUpAffineChartRing_of_eq_zero I V 0 rfl).false y
  · obtain ⟨ℓ, -, rfl⟩ := Finset.mem_image.mp haA
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨ℓ, (le_iSup₂ (f := fun (V : X.affineOpens) (h : V.1 ≤ c.U) =>
        (blowUpChartOpen I V ⟨_, c.restrict_mem_ideal V h ℓ⟩).1) V h) hxa⟩

/-! ### The chart ring of a coordinate-centre blow-up -/

/-- The pull-back `π^* : 𝒪_X(U) → 𝒪_{B_IX}(U_ℓ)` as a ring homomorphism. -/
abbrev chartPullbackHom (ℓ : Fin c.r) : Γ(X, c.U) →+* Γ(blowUp I, c.chart ℓ) :=
  ((blowUpToBase I).appLE c.U (c.chart ℓ) (c.chart_le ℓ)).hom

/-- The fraction `x_i / x_ℓ ∈ 𝒪_{B_IX}(U_ℓ)`: the unique section `y` with `π^*x_i = y · π^*x_ℓ`
(`MMP.Resolution.BlowupChartData.existsUnique_chartFraction`). -/
def chartFraction (ℓ i : Fin c.r) : Γ(blowUp I, c.chart ℓ) :=
  (c.existsUnique_chartFraction ℓ i).exists.choose

/-- On the chart `U_ℓ`, `π^*x_i = (x_i / x_ℓ) · π^*x_ℓ`. -/
theorem chartPullback_eq_chartFraction_mul (ℓ i : Fin c.r) :
    c.chartPullback ℓ (c.x i) = chartFraction c ℓ i * c.chartPullback ℓ (c.x ℓ) :=
  (c.existsUnique_chartFraction ℓ i).exists.choose_spec

/-- The `𝒪_X(U)`-algebra homomorphism `𝒪_X(U)[T_i : i ≠ ℓ] → 𝒪(U_ℓ)`, `T_i ↦ x_i / x_ℓ`. -/
def chartPresentation (ℓ : Fin c.r) :
    MvPolynomial {i : Fin c.r // i ≠ ℓ} Γ(X, c.U) →+* Γ(blowUp I, c.chart ℓ) :=
  MvPolynomial.eval₂Hom (chartPullbackHom c ℓ) fun i => chartFraction c ℓ i.1

private theorem isH1Regular_comp_of_isLocalCoordinates {X : Scheme.{u}} {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (x : Fin n → Γ(X, U))
    (hx : IsLocalCoordinates sX U x) {m : ℕ} (σ : Fin m → Fin n)
    (hσ : Function.Injective σ) :
    Koszul.IsH1Regular fun j => x (σ j) := by
  have : IsAffine U.toScheme := hU
  set h := AffineSpace.homOfVector (n := ULift.{u} (Fin n)) (U.ι ≫ sX)
    fun i => U.topIso.inv.hom (x i.down) with hh
  have : Etale h := hx
  have hflat : RingHom.Flat h.appTop.hom := HasRingHomProperty.appTop @Flat h inferInstance
  let E' : Γ(AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)), ⊤) ≅
      CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) k) :=
    (Scheme.Γ.mapIso (AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of k)).op).symm ≪≫
      Scheme.ΓSpecIso _
  let E := E'.commRingCatIsoToRingEquiv
  have hE : ∀ i, E.symm (MvPolynomial.X i) = AffineSpace.coord (Spec (.of k)) i := by
    intro i
    apply E.injective
    rw [RingEquiv.apply_symm_apply]
    change _ = (Scheme.ΓSpecIso _).hom.hom
      ((AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of k)).inv.appTop.hom
        (AffineSpace.coord (Spec (.of k)) i))
    rw [AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply, Iso.inv_hom_id,
      CommRingCat.id_apply]
  have hg : Koszul.IsH1Regular fun j =>
      AffineSpace.coord (Spec (.of k)) (ULift.up.{u} (σ j)) := by
    have := isH1Regular_map_ringEquiv E.symm _
      (isH1Regular_X_comp (R := k) (fun j => ULift.up.{u} (σ j))
        (fun a b hab => hσ (congrArg ULift.down hab)))
    simpa [hE] using this
  let := h.appTop.hom.toAlgebra
  have : Module.Flat _ _ := hflat
  have h2 := Koszul.isH1Regular_map_of_flat (S := Γ(U.toScheme, ⊤)) _ hg
  have h3 := isH1Regular_map_ringEquiv U.topIso.commRingCatIsoToRingEquiv _ h2
  convert h3 using 2 with j
  change x (σ j) = U.topIso.hom.hom (h.appTop.hom _)
  rw [hh, AffineSpace.homOfVector_appTop_coord]
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

private theorem presheaf_map_homOfLE_refl_apply (s : Γ(X, c.U)) :
    (X.presheaf.map (homOfLE (le_refl c.U)).op).hom s = s := by
  rw [show (homOfLE (le_refl c.U)).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- The chart presentation read in the localization `Γ(X, U)_{x_ℓ}`. -/
private theorem exists_chartPresentation_eq_aeval (hU : IsAffineOpen c.U) (ℓ : Fin c.r) :
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
    fun s => (congrArg (fun φ => φ.hom s) hmor :)
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

/-- **Coordinate-centre blow-up charts have precisely the expected equations.** Let
`x_1, …, x_n` be a system of local coordinates on an affine open `U` of a scheme `X` over `k`,
and let the first `r` of them generate the ideal `I|_U` of the centre. Then for every `ℓ ≤ r`
the homomorphism `𝒪_X(U)[T_i : i ≤ r, i ≠ ℓ] → 𝒪(U_ℓ)`, `T_i ↦ x_i / x_ℓ`, is surjective with
kernel generated by the `x_i - T_i x_ℓ`. (That `U_ℓ` is affine is
`MMP.Flips.ResolutionInputs.isAffineOpen_chart`.) -/
@[mmp "lem_mmp_foundation_coordinate_blowup_chart_ring"]
theorem chartPresentation_surjective_and_ker {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (hU : IsAffineOpen c.U) {n : ℕ} (x : Fin n → Γ(X, c.U)) (hx : IsLocalCoordinates sX c.U x)
    (hrn : c.r ≤ n) (hcx : ∀ i, c.x i = x (Fin.castLE hrn i)) (ℓ : Fin c.r) :
    Function.Surjective (chartPresentation c ℓ) ∧
      RingHom.ker (chartPresentation c ℓ) =
        Ideal.span (Set.range fun i : {i : Fin c.r // i ≠ ℓ} =>
          MvPolynomial.C (c.x i.1) - MvPolynomial.X i * MvPolynomial.C (c.x ℓ)) := by
  obtain ⟨Θ, hinj, hmemΘ, hsurjΘ, hcomp⟩ := exists_chartPresentation_eq_aeval c hU ℓ
  have hcard : Fintype.card {i : Fin c.r // i ≠ ℓ} = c.r - 1 := by
    simp [Fintype.card_subtype_compl]
  obtain ⟨m, hm⟩ : ∃ m, c.r = m + 1 := ⟨c.r - 1, by have := ℓ.pos; omega⟩
  let e : Fin m ≃ {i : Fin c.r // i ≠ ℓ} :=
    (Fintype.equivFinOfCardEq (hcard.trans (by omega))).symm
  let b : {i : Fin c.r // i ≠ ℓ} → Γ(X, c.U) := fun i => c.x i.1
  let σ : Fin (m + 1) → Fin n :=
    Fin.cases (Fin.castLE hrn ℓ) fun j => Fin.castLE hrn (e j).1
  have hσ : Function.Injective σ := by
    intro i j hij
    induction i using Fin.cases <;> induction j using Fin.cases
    · rfl
    · exact absurd (Fin.castLE_injective hrn hij).symm (e _).2
    · exact absurd (Fin.castLE_injective hrn hij) (e _).2
    · simp only [σ, Fin.cases_succ] at hij
      exact congrArg Fin.succ (e.injective (Subtype.ext (Fin.castLE_injective hrn hij)))
  have hf : Koszul.IsH1Regular (Fin.cases ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x ℓ))
      (fun j => b (e j)) : Fin (m + 1) → Γ(X, c.U)) := by
    convert isH1Regular_comp_of_isLocalCoordinates sX hU x hx σ hσ using 1
    funext j
    induction j using Fin.cases
    · simp only [Fin.cases_zero, σ, hcx, presheaf_map_homOfLE_refl_apply]
    · simp only [Fin.cases_succ, σ, b, hcx]
  obtain ⟨halg1, halg2⟩ := aeval_mk'_range_and_ker_of_isH1Regular e _ b hf
  have hI : I.ideal ⟨c.U, hU⟩ = Ideal.span (insert
      ((X.presheaf.map (homOfLE (le_refl c.U)).op).hom (c.x ℓ)) (Set.range b)) := by
    rw [c.generates ⟨c.U, hU⟩ le_rfl]
    congr 1
    ext y
    simp only [presheaf_map_homOfLE_refl_apply, Set.mem_range, Set.mem_insert_iff, b]
    constructor
    · rintro ⟨i, rfl⟩
      by_cases hi : i = ℓ
      · exact Or.inl (by rw [hi])
      · exact Or.inr ⟨⟨i, hi⟩, rfl⟩
    · rintro (rfl | ⟨i, rfl⟩)
      · exact ⟨ℓ, rfl⟩
      · exact ⟨i.1, rfl⟩
  rw [hI] at hmemΘ
  refine ⟨fun t => ?_, ?_⟩
  · obtain ⟨p, hp⟩ := halg1 (Θ t) (hmemΘ t)
    refine ⟨p, hinj ?_⟩
    rwa [← RingHom.comp_apply, hcomp]
  · rw [← RingHom.ker_comp_of_injective (chartPresentation c ℓ) hinj, hcomp]
    refine halg2.trans ?_
    simp only [presheaf_map_homOfLE_refl_apply, b]

/-! ### Orders under flat pullback with regular fibres -/

private theorem isLocalHom_quotient_mk_of_le_maximalIdeal {S : Type*} [CommRing S]
    [IsLocalRing S] {I : Ideal S} (h : I ≤ maximalIdeal S) : IsLocalHom (Ideal.Quotient.mk I) :=
  isLocalHom_of_le_jacobson_bot _ (by rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])

/-- For a flat local homomorphism `R → S` of local rings whose closed fibre is a regular local
ring of dimension `0`, every `𝔪_S`-adic power pulls back into the same power of `𝔪_R`. -/
theorem comap_maximalIdeal_pow_le_of_ringKrullDim_fibre_eq_zero (R S : Type*) [CommRing R]
    [IsLocalRing R] [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (hreg : IsRegularLocalRing (S ⧸ (maximalIdeal R).map (algebraMap R S)))
    (hdim : ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) = 0) (j : ℕ) :
    (maximalIdeal S ^ j).comap (algebraMap R S) ≤ maximalIdeal R ^ j := by
  have : IsLocalHom (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S))) :=
    isLocalHom_quotient_mk_of_le_maximalIdeal
      (Ideal.map_le_iff_le_comap.2 (IsLocalRing.maximalIdeal_comap _).ge)
  have hbot : maximalIdeal (S ⧸ (maximalIdeal R).map (algebraMap R S)) = ⊥ := by
    rw [← Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)]
    have := hreg.spanFinrank_maximalIdeal
    rw [hdim] at this
    exact_mod_cast this
  have hle : maximalIdeal S ≤ (maximalIdeal R).map (algebraMap R S) := by
    intro s hs
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) s ∈
        maximalIdeal (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
      (map_mem_nonunits_iff _ _).2 hs
    rwa [hbot] at this
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  intro x hx
  have : algebraMap R S x ∈ ((maximalIdeal R) ^ j).map (algebraMap R S) := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hle j hx
  rwa [← Ideal.mem_comap, Ideal.comap_map_eq_self_of_faithfullyFlat] at this

private noncomputable def quotientSpanFibreEquiv {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (I : Ideal R) (f : S) :
    (S ⧸ Ideal.span {f}) ⧸ I.map (algebraMap R (S ⧸ Ideal.span {f})) ≃+*
      (S ⧸ I.map (algebraMap R S)) ⧸ Ideal.span {Ideal.Quotient.mk (I.map (algebraMap R S)) f} :=
  (Ideal.quotEquivOfEq (by
      rw [show algebraMap R (S ⧸ Ideal.span {f}) =
          (Ideal.Quotient.mk (Ideal.span {f})).comp (algebraMap R S) from
        IsScalarTower.algebraMap_eq R S _, ← Ideal.map_map])).trans <|
    (DoubleQuot.quotQuotEquivComm (Ideal.span {f}) _).trans
      (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton]))

/-- If `J ≤ 𝔪_S` and the `𝔪`-adic powers of `S ⧸ J` pull back into those of `𝔪_R`, then so do
those of `S`. -/
theorem comap_maximalIdeal_pow_le_of_comap_quotient {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] {J : Ideal S} [IsLocalRing (S ⧸ J)]
    (hJ : J ≤ maximalIdeal S) (j : ℕ)
    (h : (maximalIdeal (S ⧸ J) ^ j).comap (algebraMap R (S ⧸ J)) ≤ maximalIdeal R ^ j) :
    (maximalIdeal S ^ j).comap (algebraMap R S) ≤ maximalIdeal R ^ j := by
  have := isLocalHom_quotient_mk_of_le_maximalIdeal hJ
  intro r hr
  apply h
  have hle : (maximalIdeal S ^ j).map (Ideal.Quotient.mk J) ≤ maximalIdeal (S ⧸ J) ^ j := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 (IsLocalRing.maximalIdeal_comap _).ge) j
  rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply R S (S ⧸ J)]
  exact hle (Ideal.mem_map_of_mem _ hr)

open Module.Flat in
/-- For a flat local homomorphism `R → S` of Noetherian local rings whose closed fibre is a
regular local ring of dimension `n`, every `𝔪_S`-adic power pulls back into the same power of
`𝔪_R`: induction on `n`, cutting the fibre by an element of `𝔪 ∖ 𝔪²` (Stacks 00MF keeps the
quotient flat), down to fibre a field, where `𝔪_S = 𝔪_R S` and faithful flatness concludes. -/
private theorem comap_maximalIdeal_pow_le_of_flat (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (n : ℕ) :
    ∀ (S : Type u) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra R S]
      [IsLocalHom (algebraMap R S)] [Module.Flat R S],
      IsRegularLocalRing (S ⧸ (maximalIdeal R).map (algebraMap R S)) →
      ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) = n →
      ∀ j : ℕ, (maximalIdeal S ^ j).comap (algebraMap R S) ≤ maximalIdeal R ^ j := by
  induction n with
  | zero =>
    intro S _ _ _ _ _ _ hreg hdim
    exact comap_maximalIdeal_pow_le_of_ringKrullDim_fibre_eq_zero R S hreg (by exact_mod_cast hdim)
  | succ n ih =>
    intro S _ _ _ _ _ _ hreg hdim j
    set 𝔫 := (maximalIdeal R).map (algebraMap R S) with h𝔫
    have : IsLocalHom (Ideal.Quotient.mk 𝔫) := isLocalHom_quotient_mk_of_le_maximalIdeal
      (Ideal.map_le_iff_le_comap.2 (IsLocalRing.maximalIdeal_comap _).ge)
    have hne : ringKrullDim (S ⧸ 𝔫) ≠ 0 := by
      rw [hdim]
      exact_mod_cast n.succ_ne_zero
    obtain ⟨x, hx, hx2⟩ :=
      SetLike.exists_of_lt (IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero hne)
    obtain ⟨hregq, hdimq⟩ := quotient_isRegularLocalRing _ x hx hx2
    have := IsRegularLocalRing.isDomain (S ⧸ 𝔫)
    have hx0 : x ≠ 0 := fun h => hx2 (h ▸ zero_mem _)
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨-, hflat⟩ :=
      mem_nonZeroDivisors_and_flat_quotient_span_singleton_of_mem_nonZeroDivisors_maximalIdeal
        (R := R) (S := S) (f := f) (mem_nonZeroDivisors_of_ne_zero hx0)
    have hfm : f ∈ maximalIdeal S := (map_mem_nonunits_iff (Ideal.Quotient.mk 𝔫) f).1 hx
    have hspan_le : Ideal.span {f} ≤ maximalIdeal S := Ideal.span_le.2 (by simpa using hfm)
    have : Nontrivial (S ⧸ Ideal.span {f}) :=
      Ideal.Quotient.nontrivial_iff.2
        (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hspan_le)
    have : IsLocalRing (S ⧸ Ideal.span {f}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {f})) :=
      isLocalHom_quotient_mk_of_le_maximalIdeal hspan_le
    have halg : algebraMap R (S ⧸ Ideal.span {f}) =
        (Ideal.Quotient.mk (Ideal.span {f})).comp (algebraMap R S) :=
      IsScalarTower.algebraMap_eq R S _
    have : IsLocalHom (algebraMap R (S ⧸ Ideal.span {f})) := by
      rw [halg]
      infer_instance
    let e : ((S ⧸ Ideal.span {f}) ⧸ (maximalIdeal R).map (algebraMap R (S ⧸ Ideal.span {f}))) ≃+*
        ((S ⧸ 𝔫) ⧸ Ideal.span {Ideal.Quotient.mk 𝔫 f}) := quotientSpanFibreEquiv (maximalIdeal R) f
    have hreg' := IsRegularLocalRing.of_ringEquiv e.symm
    have hdim' : ringKrullDim ((S ⧸ Ideal.span {f}) ⧸
        (maximalIdeal R).map (algebraMap R (S ⧸ Ideal.span {f}))) = n := by
      rw [ringKrullDim_eq_of_ringEquiv e]
      rw [hdim] at hdimq
      obtain ⟨m, hm⟩ := Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim
        ((S ⧸ 𝔫) ⧸ Ideal.span {Ideal.Quotient.mk 𝔫 f})
      rw [hm] at hdimq ⊢
      have : m + 1 = n + 1 := by exact_mod_cast hdimq
      exact congrArg _ (Nat.succ.inj this)
    exact comap_maximalIdeal_pow_le_of_comap_quotient hspan_le j
      (ih (S ⧸ Ideal.span {f}) hreg' hdim' j)

/-- **Orders are unchanged under a flat morphism with regular closed fibres.** Let
`φ : Y ⟶ X` be a flat morphism of regular locally noetherian schemes such that for every
`y ∈ Y` the fibre ring `𝒪_{Y,y}/𝔪_{φ(y)}𝒪_{Y,y}` is regular. Then
`ord_y(φ^*I) = ord_{φ(y)} I` for every ideal sheaf `I` of `X` and every `y ∈ Y`. -/
@[mmp "lem_mmp_foundation_order_preserved_regular_flat_pullback"]
theorem multAt_comap_eq {X Y : Scheme.{u}} (φ : Y ⟶ X) [Flat φ] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (hfib : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y ⧸
      (maximalIdeal (X.presheaf.stalk (φ y))).map (φ.stalkMap y).hom))
    (I : X.IdealSheafData) (y : Y) :
    multAt (I.comap φ) y = multAt I (φ y) := by
  rw [multAt, multAt, IdealSheafData.stalk_comap]
  let : Algebra (X.presheaf.stalk (φ y)) (Y.presheaf.stalk y) := (φ.stalkMap y).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (φ y)) (Y.presheaf.stalk y) := Flat.stalkMap φ y
  have : IsLocalHom (algebraMap (X.presheaf.stalk (φ y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (φ.stalkMap y).hom)
  obtain ⟨n, hn⟩ := Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim
    (Y.presheaf.stalk y ⧸ (maximalIdeal (X.presheaf.stalk (φ y))).map (φ.stalkMap y).hom)
  have hpow : ∀ j : ℕ, (maximalIdeal (Y.presheaf.stalk y) ^ j).comap (φ.stalkMap y).hom =
      maximalIdeal (X.presheaf.stalk (φ y)) ^ j := by
    intro j
    refine le_antisymm (comap_maximalIdeal_pow_le_of_flat (X.presheaf.stalk (φ y)) n
      (Y.presheaf.stalk y) (hfib y) hn j) ?_
    refine Ideal.map_le_iff_le_comap.1 ?_
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2
      (IsLocalRing.maximalIdeal_comap _).ge) j
  simp only [idealOrder, Ideal.map_le_iff_le_comap, hpow]

end MMP.Flips.ResolutionInputs

end
