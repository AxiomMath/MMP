module

public import MMP.RingTheory.Kaehler.LogLattice
public import MMP.AlgebraicGeometry.DeRham.RationalForms.Gluing
public import MMP.AlgebraicGeometry.Intersection.CartierRestriction
public import MMP.AlgebraicGeometry.Morphisms.SmoothLocalRings
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.ChartStalkBasis
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Place.ChartForms

/-!
# Chart coefficients of a rational form from its lattices at prime divisors

Let `W` be a chart of a relative simple normal crossing divisor `S` on a normal integral scheme
`Y` over `k`, with coordinates `tₗ`, the first `r` of them local equations of the components of
`S` through the chart. The rational chart forms `tₗ⁻¹ dtₗ` (`l < r`) and `dtₗ` (`l ≥ r`) are a
basis of `Ω_{k(Y)/k}`.

Let `β` be a rational `p`-form which, at every prime divisor `E` meeting an affine open `W' ⊆ W`,
lies in the wedges of the regular lattice of `𝒪_{Y,E}`, and, when `E` is a component of `S`, in
the maximal ideal times the wedges of the logarithmic lattice. Then the coordinates of `β` in the
wedges of the chart basis are functions on `W'` in the ideal of `S`: at a component `E` of `S`
the local equation of `E` is a uniformizer and the logarithmic lattice is spanned by the chart
forms, and the local equations of the other components are units; algebraic Hartogs then extends
the coordinates divided by `∏ tᵢ` over `W'`. This is the input of the membership criterion
`MMP.FourfoldProofs.FractionalLogComplexProof.mem_relativeLogForms_of_ratForm_eq`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_basis_chartForm`: the chart basis.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_chart_coeffs_of_le`: the coordinates in the
  ideal of a twist `S` whose components are components of `D`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_chart_coeffs`: the coordinates in the ideal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential TopologicalSpace IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- **The chart basis.** On a chart `W` with coordinates `tₗ`, the rational chart forms
`tₗ⁻¹ dtₗ` (`l < r`) and `dtₗ` (`l ≥ r`) are a basis of `Ω_{k(Y)/k}`, and the coordinates are
nonzero in `k(Y)`. -/
theorem exists_basis_chartForm [IsIntegral Y] (f : Y ⟶ Spec (.of k)) {n : ℕ}
    (W : Y.affineOpens) [Nonempty (W : Y.Opens)] (V : (Spec (.of k)).affineOpens)
    (e : (W : Y.Opens) ≤ f ⁻¹ᵁ (V : (Spec (.of k)).Opens)) (t : Fin n → Γ(Y, W))
    (hb : letI := (f.appLE V W e).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(Y, W) Ω[Γ(Y, W)⁄Γ(Spec (.of k), V)],
        ∀ i, b i = KaehlerDifferential.D Γ(Spec (.of k), V) Γ(Y, W) (t i)) (r : ℕ) :
    letI := MMP.Mori.functionFieldAlgebra f
    (∀ l, Y.germToFunctionField W (t l) ≠ 0) ∧
      ∃ B : Module.Basis (Fin n) Y.functionField Ω[Y.functionField⁄k], ⇑B = chartForm f W t r := by
  classical
  let := MMP.Mori.functionFieldAlgebra f
  let := MMP.Mori.sectionAlgebra f W
  have := MMP.Mori.isScalarTower_section_functionField f (W : Y.Opens)
  have := functionField_isFractionRing_of_isAffineOpen Y (W : Y.Opens) W.2
  obtain ⟨b, hb'⟩ := exists_basis_D_section_of_chart f W V e t hb
  let B0 := regBasis k (K := Y.functionField) b
  have hB0 : ∀ l, B0 l = D k Y.functionField (Y.germToFunctionField W (t l)) := fun l => by
    rw [regBasis_apply, hb', KaehlerDifferential.map_D]
    rfl
  have hne : ∀ l, Y.germToFunctionField W (t l) ≠ 0 := fun l h =>
    B0.ne_zero l (by rw [hB0, h, map_zero])
  let w : Fin n → Y.functionFieldˣ := fun l =>
    if (l : ℕ) < r then (Units.mk0 _ (hne l))⁻¹ else 1
  refine ⟨hne, B0.unitsSMul w, funext fun l => ?_⟩
  rw [Module.Basis.unitsSMul_apply, hB0]
  unfold chartForm
  by_cases h : (l : ℕ) < r <;> simp [w, h, Units.smul_def]

/-- **Chart coefficients in the ideal of a twist.** Let `W` be a chart of the relative simple
normal crossing divisor `D` and `S` a divisor whose components are components of `D`. A rational
`p`-form `β` which, at every prime divisor `E` meeting the affine open `W' ⊆ W`, lies in the wedges
of the regular lattice of `𝒪_{Y,E}` if `E` is not a component of `D`, in the wedges of the
logarithmic lattice if it is, and in the maximal ideal times these wedges if `E` is a component of
`S`, is a combination `∑_K c_K β_K` of the wedges of the rational chart forms, with every `c_K` a
function on `W'` in the ideal of `S`. -/
theorem exists_chart_coeffs_of_le [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ Spec (.of k)) {n : ℕ} (D S : MMP.Mori.Divisor Y)
    (hSD : ∀ E ∈ S.support, E ∈ D.support) (W : Y.affineOpens) [Nonempty (W : Y.Opens)]
    (V : (Spec (.of k)).affineOpens)
    (e : (W : Y.Opens) ≤ f ⁻¹ᵁ (V : (Spec (.of k)).Opens)) (t : Fin n → Γ(Y, W))
    (hb : letI := (f.appLE V W e).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(Y, W) Ω[Γ(Y, W)⁄Γ(Spec (.of k), V)],
        ∀ i, b i = KaehlerDifferential.D Γ(Spec (.of k), V) Γ(Y, W) (t i))
    {r : ℕ} (hr : r ≤ n) (j : Fin r → MMP.Mori.PrimeDivisor Y)
    (hj : ∀ i, (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)})
    (hDW : D.suppIdeal.ideal W = Ideal.span {∏ i, t (Fin.castLE hr i)})
    (W' : Y.affineOpens) (hW' : (W' : Y.Opens) ≤ W) [Nonempty (W' : Y.Opens)] (p : ℕ)
    (β : letI := MMP.Mori.functionFieldAlgebra f; ⋀[Y.functionField]^p Ω[Y.functionField⁄k])
    (hβ : ∀ E : MMP.Mori.PrimeDivisor Y, (E.support ∩ W').Nonempty →
      letI := MMP.Mori.functionFieldAlgebra f
      letI := MMP.Mori.stalkAlgebra f E.genericPoint
      haveI := MMP.Mori.isScalarTower_stalk_functionField f E.genericPoint
      (E ∉ D.support → β ∈ wedgeSpan E.localRing (regLattice k E.localRing) p) ∧
      (E ∈ D.support → β ∈ wedgeSpan E.localRing (logLattice k E.localRing) p) ∧
      (E ∈ S.support → β ∈ maximalIdeal E.localRing •
          wedgeSpan E.localRing (logLattice k E.localRing) p)) :
    letI := MMP.Mori.functionFieldAlgebra f
    ∃ c : {K : Finset (Fin n) // K.card = p} → Γ(Y, W'), (∀ K, c K ∈ S.suppIdeal.ideal W') ∧
      β = ∑ K, Y.germToFunctionField W' (c K) • exteriorPower.ιMulti Y.functionField p
        fun l => chartForm f W t r (K.1.orderEmbOfFin K.2 l) := by
  classical
  let := MMP.Mori.functionFieldAlgebra f
  obtain ⟨hne, B, hB⟩ := exists_basis_chartForm f W V e t hb r
  set a : Set.powersetCard (Fin n) p → Y.functionField := fun T => (B.exteriorPower p).repr β T
  -- at a prime divisor meeting `W'`, the coordinates are regular, and in the maximal ideal along
  -- the components of `S`
  have hloc : ∀ T (E : MMP.Mori.PrimeDivisor Y), (E.support ∩ W').Nonempty →
      ∃ r₀ : E.localRing, algebraMap E.localRing Y.functionField r₀ = a T ∧
        (E ∈ S.support → r₀ ∈ maximalIdeal E.localRing) := by
    intro T E hE
    set y := E.genericPoint with hy
    have hyW' : y ∈ (W' : Y.Opens) := E.genericPoint_mem_of_nonempty hE
    have hyW : y ∈ (W : Y.Opens) := hW' hyW'
    let := MMP.Mori.stalkAlgebra f y
    have := MMP.Mori.isScalarTower_stalk_functionField f y
    have hgerm : ∀ l, algebraMap (Y.presheaf.stalk y) Y.functionField
        (Y.presheaf.germ (W : Y.Opens) y hyW (t l)) = Y.germToFunctionField W (t l) := fun l =>
      Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hyW (t l)
    -- the regular lattice lies in the span of the chart basis
    have hregB : regLattice k (Y.presheaf.stalk y) ≤
        Submodule.span (Y.presheaf.stalk y) (Set.range B) := by
      rw [regLattice, Submodule.span_le]
      rintro _ ⟨a0, rfl⟩
      obtain ⟨bR, hbR⟩ := exists_basis_D_stalk_of_chart f W V e t hb hyW
      have h1 := map_mem_span_of_basis k (L := Y.functionField) bR (KaehlerDifferential.D k _ a0)
      rw [KaehlerDifferential.map_D] at h1
      refine Submodule.span_le.2 ?_ h1
      rintro _ ⟨l, rfl⟩
      simp only [Function.comp_apply, hbR, KaehlerDifferential.map_D, hgerm]
      by_cases hl : (l : ℕ) < r
      · have e1 : KaehlerDifferential.D k Y.functionField (Y.germToFunctionField W (t l)) =
            Y.presheaf.germ (W : Y.Opens) y hyW (t l) • B l := by
          rw [hB, chartForm, ite_eq_left hl, ← algebraMap_smul Y.functionField, hgerm, smul_smul,
            mul_inv_cancel₀ (hne l), one_smul]
        rw [e1]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
      · refine Submodule.subset_span ⟨l, ?_⟩
        rw [hB, chartForm, ite_eq_right hl, one_smul]
    by_cases hED : E ∈ D.support
    · -- `E` is a coordinate component, and its equation is a uniformizer
      have hyE : y ∈ E.support := by
        rw [hy, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      obtain ⟨i₀, hEj⟩ := exists_eq_of_mem_chart t hr j hj hDW hED hyW hyE
      have := E.isDiscreteValuationRing_localRing
      set σ := Y.presheaf.germ (W : Y.Opens) y hyW (t (Fin.castLE hr i₀)) with hσ
      have hmax : maximalIdeal (Y.presheaf.stalk y) = Ideal.span {σ} := by
        have ht : E.idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i₀)} := hEj ▸ hj i₀
        exact maximalIdeal_localRing_eq_span E W hyW ht
      have hσirr : Irreducible σ := (IsDiscreteValuationRing.irreducible_iff_uniformizer σ).2 hmax
      have hσL : algebraMap (Y.presheaf.stalk y) Y.functionField σ ≠ 0 := by
        rw [hσ, hgerm]
        exact hne _
      -- the logarithmic lattice lies in the span of the chart basis
      have hlogB : logLattice k (Y.presheaf.stalk y) ≤
          Submodule.span (Y.presheaf.stalk y) (Set.range B) := by
        rw [logLattice, Submodule.span_le]
        rintro _ ⟨a0, rfl⟩
        by_cases ha : a0 = 0
        · simp [ha]
        obtain ⟨m, v, hav⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hσirr
        have haL : algebraMap (Y.presheaf.stalk y) Y.functionField a0 ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective _ Y.functionField)).2 ha
        have key := inv_smul_D_eq_of_eq_mul_pow k (A := Y.presheaf.stalk y)
          (B := Y.presheaf.stalk y) (L := Y.functionField) v.isUnit (t := a0) (s := σ) (e := m)
          hav (inv_mul_cancel₀ hσL) (inv_mul_cancel₀ haL)
        change (algebraMap _ Y.functionField a0)⁻¹ •
          KaehlerDifferential.D k Y.functionField (algebraMap _ _ a0) ∈ _
        rw [key]
        refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span
          ⟨Fin.castLE hr i₀, ?_⟩)) (Submodule.smul_mem _ _ (hregB (D_mem_regLattice _)))
        rw [hB, chartForm, ite_eq_left (show ((Fin.castLE hr i₀ : Fin n) : ℕ) < r from i₀.2), hσ,
          hgerm]
      have hN : ∀ v ∈ logLattice k (Y.presheaf.stalk y), ∀ l,
          B.repr v l ∈ (algebraMap (Y.presheaf.stalk y) Y.functionField).range :=
        fun v hv l => repr_mem_range_of_mem_span B (hlogB hv) l
      obtain ⟨r₀, hr₀⟩ := repr_mem_range_of_mem_wedgeSpan B
        (wedgeSpan_mono hlogB p ((hβ E hE).2.1 hED)) T
      refine ⟨r₀, hr₀, fun hES => ?_⟩
      obtain ⟨r₁, hr₁, hr₁a⟩ := exists_mem_ideal_repr_eq B _ hN _ ((hβ E hE).2.2 hES) T
      rwa [IsFractionRing.injective _ Y.functionField (hr₀.trans hr₁a.symm)]
    · obtain ⟨r₀, hr₀⟩ := repr_mem_range_of_mem_wedgeSpan B
        (wedgeSpan_mono hregB p ((hβ E hE).1 hED)) T
      exact ⟨r₀, hr₀, fun hES => absurd (hSD E hES) hED⟩
  -- the coordinates are functions on `W'`
  have hreg : ∀ T, ∃ d : Γ(Y, W'), Y.germToFunctionField W' d = a T := fun T =>
    exists_germToFunctionField_eq_of_forall_localRing (W' : Y.Opens) _ fun E hE => by
      obtain ⟨r₀, hr₀, -⟩ := hloc T E hE
      exact ⟨r₀, hr₀⟩
  choose d hd using hreg
  refine ⟨fun K => d ⟨K.1, K.2⟩, fun K => ?_, ?_⟩
  · -- the coordinates vanish along the components of `S`
    rw [MMP.Intersection.suppIdeal_eq_finsetInf, finsetInf_ideal, ← Ideal.span_singleton_le_iff_mem]
    refine Finset.le_inf fun E hES => ?_
    rw [Ideal.span_singleton_le_iff_mem, MMP.Mori.PrimeDivisor.mem_ideal_idealSheaf_iff]
    intro hη hηb
    have hE : (E.support ∩ (W' : Y.Opens)).Nonempty := ⟨E.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl, hη⟩
    obtain ⟨r₀, hr₀, hm⟩ := hloc ⟨K.1, K.2⟩ E hE
    have hgd : Y.presheaf.germ (W' : Y.Opens) E.genericPoint hη (d ⟨K.1, K.2⟩) = r₀ := by
      refine IsFractionRing.injective _ Y.functionField ?_
      rw [Scheme.algebraMap_germ_eq_germToFunctionField, hd, hr₀]
    have hu := (Y.mem_basicOpen _ _ hη).1 hηb
    rw [hgd] at hu
    exact (maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ (hm hES) hu)
  · conv_lhs => rw [← (B.exteriorPower p).sum_repr β]
    let eK : Set.powersetCard (Fin n) p ≃ {K : Finset (Fin n) // K.card = p} :=
      Equiv.subtypeEquivRight fun _ => Iff.rfl
    conv_rhs => rw [← eK.sum_comp]
    refine Finset.sum_congr rfl fun T _ => ?_
    change _ = Y.germToFunctionField W' (d ⟨_, _⟩) • _
    rw [hd, exteriorPower.basis_apply, exteriorPower.ιMulti_family, hB]
    rfl

/-- **Chart coefficients in the ideal of the divisor.** A rational `p`-form `β` which, at every
prime divisor `E` meeting the affine open `W'` of the chart `W` of `S`, lies in the wedges of the
regular lattice of `𝒪_{Y,E}` and, when `E` is a component of `S`, in the maximal ideal times the
wedges of the logarithmic lattice, is a combination `∑_K c_K β_K` of the wedges of the rational
chart forms, with every `c_K` a function on `W'` in the ideal of `S`. -/
theorem exists_chart_coeffs [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ Spec (.of k)) {n : ℕ} (S : MMP.Mori.Divisor Y) (W : Y.affineOpens)
    [Nonempty (W : Y.Opens)] (V : (Spec (.of k)).affineOpens)
    (e : (W : Y.Opens) ≤ f ⁻¹ᵁ (V : (Spec (.of k)).Opens)) (t : Fin n → Γ(Y, W))
    (hb : letI := (f.appLE V W e).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(Y, W) Ω[Γ(Y, W)⁄Γ(Spec (.of k), V)],
        ∀ i, b i = KaehlerDifferential.D Γ(Spec (.of k), V) Γ(Y, W) (t i))
    {r : ℕ} (hr : r ≤ n) (j : Fin r → MMP.Mori.PrimeDivisor Y)
    (hjS : ∀ i, j i ∈ S.support ∧ (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)})
    (hSW : S.suppIdeal.ideal W = Ideal.span {∏ i, t (Fin.castLE hr i)})
    (W' : Y.affineOpens) (hW' : (W' : Y.Opens) ≤ W) [Nonempty (W' : Y.Opens)] (p : ℕ)
    (β : letI := MMP.Mori.functionFieldAlgebra f; ⋀[Y.functionField]^p Ω[Y.functionField⁄k])
    (hβ : ∀ E : MMP.Mori.PrimeDivisor Y, (E.support ∩ W').Nonempty →
      letI := MMP.Mori.functionFieldAlgebra f
      letI := MMP.Mori.stalkAlgebra f E.genericPoint
      haveI := MMP.Mori.isScalarTower_stalk_functionField f E.genericPoint
      β ∈ wedgeSpan E.localRing (regLattice k E.localRing) p ∧
        (E ∈ S.support → β ∈ maximalIdeal E.localRing •
          wedgeSpan E.localRing (logLattice k E.localRing) p)) :
    letI := MMP.Mori.functionFieldAlgebra f
    ∃ c : {K : Finset (Fin n) // K.card = p} → Γ(Y, W'), (∀ K, c K ∈ S.suppIdeal.ideal W') ∧
      β = ∑ K, Y.germToFunctionField W' (c K) • exteriorPower.ιMulti Y.functionField p
        fun l => chartForm f W t r (K.1.orderEmbOfFin K.2 l) := by
  refine exists_chart_coeffs_of_le f S S (fun _ h => h) W V e t hb hr j (fun i => (hjS i).2) hSW W'
    hW' p β
    fun E hE => ⟨fun _ => (hβ E hE).1, fun hES => Submodule.smul_le_right ((hβ E hE).2 hES),
      (hβ E hE).2⟩

end MMP.FourfoldProofs.FractionalLogComplexProof
