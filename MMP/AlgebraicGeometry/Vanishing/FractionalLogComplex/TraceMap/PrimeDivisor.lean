module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.TraceMap.CoverPlace
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Place.RootFactor
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Place.IntegralRoots
public import MMP.AlgebraicGeometry.Singularities.Snc.ReducedPreimageComponents

/-!
# The trace map of the fractional logarithmic complex at the prime divisors

Let `g₀` be a local generator of `𝒪_X(-M)` near a point with `g₀^N = ψ v ∏ₖ τₖ^{bₖ}` in the
function field (`v` a unit, `τₖ` local equations of the components `jₖ` of `D`, `bₖ = Bn(jₖ)`), and
`z^N = f^* ψ` in the function field of the cover. For a section `ω'` of `Ω^p_Y(log S')(-S')` the
form `β = Tr((z / f^* g₀) ω')` lies, at a prime divisor `E` of `X` off `D`, in the wedges of the
regular lattice of `𝒪_{X,E}`: `(z / f^* g₀)^N = f^*(v ∏ τₖ^{bₖ})⁻¹` and the `τₖ` are units at `E`.
At a component `E = j_{k₀}` of `D` not in `S`, with `b_{k₀} < N`, it lies in the wedges of the
logarithmic lattice. At a component `E = j_{k₀}` of `S`, with `b_{k₀} = 0`, it is `h_S` times the
trace of `(z / f^*(g₀ h_S)) ω'`, `h_S = ∏_{jₖ ∈ S} τₖ`, so it lies in `𝔪_E` times the wedges of the
logarithmic lattice.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_mem_regLattice_of_factorization`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_mem_logLattice_of_factorization_of_notMem`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_mem_maximalIdeal_smul_logLattice_of_mem`:
  the case of a component of `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing KaehlerDifferential TopologicalSpace

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsFinite f] [Surjective f]
  [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]

open scoped Classical in
/-- **Off `D`, the trace map lands in the regular lattice.** -/
theorem formsTrace_mem_regLattice_of_factorization (n : ℕ) [SmoothOfRelativeDimension n sX]
    [SmoothOfRelativeDimension n (f ≫ sX)] {D S : MMP.Mori.Divisor X}
    (hSD : ∀ E ∈ S.support, E ∈ D.support)
    (S' : MMP.Mori.Divisor Y) (hS' : S'.IsRelativeSNC n (f ≫ sX)) [Nonempty (cU S')]
    (hS'def : ∀ E' : MMP.Mori.PrimeDivisor Y, S' E' =
      if ∃ E ∈ S.support, f E'.genericPoint = E.genericPoint then 1 else 0)
    (W₂ : X.affineOpens) [Nonempty (W₂ : X.Opens)] {r : ℕ} (τ : Fin r → Γ(X, W₂))
    (j : Fin r → MMP.Mori.PrimeDivisor X) (hjD : ∀ k, j k ∈ D.support)
    (hτ : ∀ k, (j k).idealSheaf.ideal W₂ = Ideal.span {τ k}) {v : Γ(X, W₂)} (hv : IsUnit v)
    (b : Fin r → ℕ) {N : ℕ} (hN : N ≠ 0) (ψK G : X.functionField) (hψK : ψK ≠ 0)
    (hG : G ^ N = ψK * X.germToFunctionField (W₂ : X.Opens) (v * ∏ k, τ k ^ b k))
    (z : Y.functionField) (hz : z ^ N = AlgebraicGeometry.functionFieldMap f ψK)
    (p : ℕ) {W₀ : Y.Opens}
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU S').ι ≫ f ≫ sX)).piece
      (p : ℤ)).val.obj (op ((cU S').ι ⁻¹ᵁ W₀))}
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n (f ≫ sX) S' hS' S'.suppIdeal p W₀)
    (O : (cU S').toScheme.affineOpens) (hO : (O : (cU S').toScheme.Opens) ≤ (cU S').ι ⁻¹ᵁ W₀)
    [Nonempty (O : (cU S').toScheme.Opens)]
    (E : MMP.Mori.PrimeDivisor X) (hEW : (E.support ∩ (W₂ : X.Opens)).Nonempty)
    (hW₀ : ∀ y : Y, f y = E.genericPoint → y ∈ W₀)
    (hED : E ∉ D.support) :
    letI := MMP.Mori.stalkAlgebra sX E.genericPoint
    letI := MMP.Mori.functionFieldAlgebra sX
    letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    letI := MMP.Mori.functionFieldMapAlgebra f
    haveI := MMP.Mori.isScalarTower_functionFieldMap sX f
    haveI := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
    haveI := finiteDimensional_functionFieldMap f
    haveI := isSeparable_functionFieldMap sX f
    formsTrace k X.functionField Y.functionField p
        ((z * (AlgebraicGeometry.functionFieldMap f G)⁻¹) •
          openFormsMap (cU S') (f ≫ sX) p (ratForm ((cU S').ι ≫ f ≫ sX) p O
          ((((cU S').ι ≫ f ≫ sX).relativeDifferentialForms (p : ℤ)).presheaf.map
            (homOfLE hO).op ω))) ∈
      wedgeSpan E.localRing (regLattice k E.localRing (L := X.functionField)) p := by
  classical
  have hηW : E.genericPoint ∈ (W₂ : X.Opens) := E.genericPoint_mem_of_nonempty hEW
  have hτu : ∀ k, IsUnit (X.presheaf.germ (W₂ : X.Opens) E.genericPoint hηW (τ k)) := fun k =>
    isUnit_germ_of_notMem_support (j k) W₂ (hτ k) hηW fun h =>
      hED ((eq_of_genericPoint_mem_support h) ▸ hjD k)
  have hvu : IsUnit (X.presheaf.germ (W₂ : X.Opens) E.genericPoint hηW v) := hv.map _
  set τ' : Fin r → E.localRing := fun k => X.presheaf.germ (W₂ : X.Opens) E.genericPoint hηW (τ k)
  obtain ⟨a₀, ha₀⟩ := inv_mem_range_of_isUnit (K := X.functionField) hvu hτu b ∅ N
  have hden : X.germToFunctionField (W₂ : X.Opens) (v * ∏ k, τ k ^ b k) =
      algebraMap E.localRing X.functionField
        (zDenom (X.presheaf.germ (W₂ : X.Opens) E.genericPoint hηW v) τ' b ∅ N) := by
    rw [zDenom, Finset.prod_empty, one_pow, mul_one, ← Scheme.algebraMap_germ_eq_germToFunctionField
      (X := X) hηW]
    simp only [τ', map_mul, map_prod, map_pow]
  have hG0 : AlgebraicGeometry.functionFieldMap f G ≠ 0 := by
    refine (map_ne_zero _).2 fun h0 => ?_
    have h1 := hG
    rw [h0, zero_pow hN, hden] at h1
    have hd0 : algebraMap E.localRing X.functionField
        (zDenom (X.presheaf.germ (W₂ : X.Opens) E.genericPoint hηW v) τ' b ∅ N) ≠ 0 :=
      ((isUnit_zDenom hvu hτu b ∅ N).map _).ne_zero
    exact mul_ne_zero hψK hd0 h1.symm
  have hlamN : (z * (AlgebraicGeometry.functionFieldMap f G)⁻¹) ^ N =
      AlgebraicGeometry.functionFieldMap f (algebraMap E.localRing X.functionField a₀) := by
    rw [ha₀, mul_pow, inv_pow, hz, ← map_pow, hG, hden, map_mul, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ ((map_ne_zero _).2 hψK), one_mul, map_inv₀]
  refine formsTrace_smul_mem_wedgeSpan_regLattice sX f n S' hS' p hω O hO E
    hW₀ (fun y hy F hF => ?_) _ fun y hy => ?_
  · obtain ⟨E', rfl⟩ := exists_primeDivisor_genericPoint_eq_of_map_eq f E hy
    exact notMem_support_of_map_genericPoint_eq f hS'def (fun h => hED (hSD E h)) hy hF
  · obtain ⟨r', hr', -⟩ := exists_stalk_eq_of_pow_eq_functionFieldMap f hy hN hlamN
    exact ⟨r', hr'⟩

open scoped Classical in
/-- **At a component of `D` not in `S`.** If `E = j k₀` is not a component of `S` and
`b k₀ < N`, the trace map lands in the logarithmic lattice. -/
theorem formsTrace_mem_logLattice_of_factorization_of_notMem (n : ℕ)
    [SmoothOfRelativeDimension n sX] [SmoothOfRelativeDimension n (f ≫ sX)]
    {S : MMP.Mori.Divisor X}
    (S' : MMP.Mori.Divisor Y) (hS' : S'.IsRelativeSNC n (f ≫ sX)) [Nonempty (cU S')]
    (hS'def : ∀ E' : MMP.Mori.PrimeDivisor Y, S' E' =
      if ∃ E ∈ S.support, f E'.genericPoint = E.genericPoint then 1 else 0)
    (W₂ : X.affineOpens) [Nonempty (W₂ : X.Opens)] {r : ℕ} (τ : Fin r → Γ(X, W₂))
    (j : Fin r → MMP.Mori.PrimeDivisor X)
    (hτ : ∀ k, (j k).idealSheaf.ideal W₂ = Ideal.span {τ k}) {v : Γ(X, W₂)} (hv : IsUnit v)
    (b : Fin r → ℕ) {N : ℕ} (hN : N ≠ 0) (ψK G : X.functionField) (hψK : ψK ≠ 0)
    (hG : G ^ N = ψK * X.germToFunctionField (W₂ : X.Opens) (v * ∏ k, τ k ^ b k))
    (z : Y.functionField) (hz : z ^ N = AlgebraicGeometry.functionFieldMap f ψK)
    (p : ℕ) {W₀ : Y.Opens}
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU S').ι ≫ f ≫ sX)).piece
      (p : ℤ)).val.obj (op ((cU S').ι ⁻¹ᵁ W₀))}
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n (f ≫ sX) S' hS' S'.suppIdeal p W₀)
    (O : (cU S').toScheme.affineOpens) (hO : (O : (cU S').toScheme.Opens) ≤ (cU S').ι ⁻¹ᵁ W₀)
    [Nonempty (O : (cU S').toScheme.Opens)]
    (E : MMP.Mori.PrimeDivisor X) (hEW : (E.support ∩ (W₂ : X.Opens)).Nonempty)
    (hW₀ : ∀ y : Y, f y = E.genericPoint → y ∈ W₀)
    {k₀ : Fin r} (hk₀ : j k₀ = E) (hES : E ∉ S.support) (hb : b k₀ < N)
    (hjinj : Function.Injective j) :
    letI := MMP.Mori.stalkAlgebra sX E.genericPoint
    letI := MMP.Mori.functionFieldAlgebra sX
    letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    letI := MMP.Mori.functionFieldMapAlgebra f
    haveI := MMP.Mori.isScalarTower_functionFieldMap sX f
    haveI := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
    haveI := finiteDimensional_functionFieldMap f
    haveI := isSeparable_functionFieldMap sX f
    formsTrace k X.functionField Y.functionField p
        ((z * (AlgebraicGeometry.functionFieldMap f G)⁻¹) •
          openFormsMap (cU S') (f ≫ sX) p (ratForm ((cU S').ι ≫ f ≫ sX) p O
          ((((cU S').ι ≫ f ≫ sX).relativeDifferentialForms (p : ℤ)).presheaf.map
            (homOfLE hO).op ω))) ∈
      wedgeSpan E.localRing (logLattice k E.localRing (L := X.functionField)) p := by
  classical
  have hηW : E.genericPoint ∈ (W₂ : X.Opens) := E.genericPoint_mem_of_nonempty hEW
  subst hk₀
  have hτu : ∀ k, k ≠ k₀ → IsUnit (X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW (τ k)) :=
    fun k hk => isUnit_germ_of_notMem_support (j k) W₂ (hτ k) hηW fun h =>
      hk (hjinj (eq_of_genericPoint_mem_support h).symm)
  have hvu : IsUnit (X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW v) := hv.map _
  have ht := maximalIdeal_localRing_eq_span (j k₀) W₂ hηW (hτ k₀)
  have htm : X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW (τ k₀) ∈
      maximalIdeal (j k₀).localRing := ht ▸ Ideal.mem_span_singleton_self _
  have := (j k₀).isDiscreteValuationRing_localRing
  have ht0 : X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW (τ k₀) ≠ 0 := by
    intro h0
    rw [h0, Set.singleton_zero, Ideal.span_zero] at ht
    exact IsDiscreteValuationRing.not_a_field _ ht
  set τ' : Fin r → (j k₀).localRing := fun k =>
    X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW (τ k)
  obtain ⟨a₀, ha₀m, ha₀⟩ := pow_mul_inv_mem_maximalIdeal_of_lt (K := X.functionField) hvu htm ht0
    rfl hτu b (Finset.notMem_empty k₀) hb
  have hden : X.germToFunctionField (W₂ : X.Opens) (v * ∏ k, τ k ^ b k) =
      algebraMap (j k₀).localRing X.functionField
        (zDenom (X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW v) τ' b ∅ N) := by
    rw [zDenom, Finset.prod_empty, one_pow, mul_one, ← Scheme.algebraMap_germ_eq_germToFunctionField
      (X := X) hηW]
    simp only [τ', map_mul, map_prod, map_pow]
  have htK : X.germToFunctionField (W₂ : X.Opens) (τ k₀) = algebraMap (j k₀).localRing
      X.functionField (X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW (τ k₀)) :=
    (Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hηW _).symm
  have hlamN : (AlgebraicGeometry.functionFieldMap f (X.germToFunctionField (W₂ : X.Opens) (τ k₀)) *
      (z * (AlgebraicGeometry.functionFieldMap f G)⁻¹)) ^ N =
      AlgebraicGeometry.functionFieldMap f (algebraMap (j k₀).localRing X.functionField a₀) := by
    have hG' : AlgebraicGeometry.functionFieldMap f G ^ N =
        AlgebraicGeometry.functionFieldMap f ψK * AlgebraicGeometry.functionFieldMap f
          (algebraMap (j k₀).localRing X.functionField
            (zDenom (X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW v) τ' b ∅ N)) := by
      rw [← map_pow, hG, hden, map_mul]
    rw [ha₀, mul_pow, mul_pow, inv_pow, hz, hG', mul_inv,
      ← mul_assoc (AlgebraicGeometry.functionFieldMap f ψK),
      mul_inv_cancel₀ ((map_ne_zero _).2 hψK), one_mul, htK]
    simp only [map_mul, map_inv₀, map_pow]
    rfl
  refine formsTrace_smul_mem_wedgeSpan_logLattice_of_notMem sX f n S' hS' p hω O hO (j k₀)
    hW₀ W₂ hηW (τ k₀) ht (fun y hy F hF => ?_) _ fun y hy => ?_
  · obtain ⟨E', rfl⟩ := exists_primeDivisor_genericPoint_eq_of_map_eq f (j k₀) hy
    exact notMem_support_of_map_genericPoint_eq f hS'def hES hy hF
  · obtain ⟨r', hr', hm⟩ := exists_stalk_eq_of_pow_eq_functionFieldMap f hy hN hlamN
    exact ⟨r', hm ha₀m, hr'⟩

open scoped Classical in
/-- **At a component of `S`.** If `E = j k₀` is a component of `S` and `b k₀ = 0`, the trace map
lands in `𝔪_E` times the logarithmic lattice. -/
theorem formsTrace_mem_maximalIdeal_smul_logLattice_of_mem (n : ℕ)
    [SmoothOfRelativeDimension n sX] [SmoothOfRelativeDimension n (f ≫ sX)]
    {S : MMP.Mori.Divisor X}
    (S' : MMP.Mori.Divisor Y) (hS' : S'.IsRelativeSNC n (f ≫ sX)) [Nonempty (cU S')]
    (hS'def : ∀ E' : MMP.Mori.PrimeDivisor Y, S' E' =
      if ∃ E ∈ S.support, f E'.genericPoint = E.genericPoint then 1 else 0)
    (W₂ : X.affineOpens) [Nonempty (W₂ : X.Opens)] {r : ℕ} (τ : Fin r → Γ(X, W₂))
    (j : Fin r → MMP.Mori.PrimeDivisor X)
    (hτ : ∀ k, (j k).idealSheaf.ideal W₂ = Ideal.span {τ k}) {v : Γ(X, W₂)} (hv : IsUnit v)
    (b : Fin r → ℕ) {N : ℕ} (hN : N ≠ 0) (ψK G : X.functionField) (hψK : ψK ≠ 0)
    (hG : G ^ N = ψK * X.germToFunctionField (W₂ : X.Opens) (v * ∏ k, τ k ^ b k))
    (z : Y.functionField) (hz : z ^ N = AlgebraicGeometry.functionFieldMap f ψK)
    (p : ℕ) {W₀ : Y.Opens}
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU S').ι ≫ f ≫ sX)).piece
      (p : ℤ)).val.obj (op ((cU S').ι ⁻¹ᵁ W₀))}
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n (f ≫ sX) S' hS' S'.suppIdeal p W₀)
    (O : (cU S').toScheme.affineOpens) (hO : (O : (cU S').toScheme.Opens) ≤ (cU S').ι ⁻¹ᵁ W₀)
    [Nonempty (O : (cU S').toScheme.Opens)]
    (E : MMP.Mori.PrimeDivisor X) (hEW : (E.support ∩ (W₂ : X.Opens)).Nonempty)
    (hW₀ : ∀ y : Y, f y = E.genericPoint → y ∈ W₀)
    {k₀ : Fin r} (hk₀ : j k₀ = E) (hES : E ∈ S.support) (hb : b k₀ = 0)
    (hjinj : Function.Injective j) :
    letI := MMP.Mori.stalkAlgebra sX E.genericPoint
    letI := MMP.Mori.functionFieldAlgebra sX
    letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    letI := MMP.Mori.functionFieldMapAlgebra f
    haveI := MMP.Mori.isScalarTower_functionFieldMap sX f
    haveI := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
    haveI := finiteDimensional_functionFieldMap f
    haveI := isSeparable_functionFieldMap sX f
    formsTrace k X.functionField Y.functionField p
        ((z * (AlgebraicGeometry.functionFieldMap f G)⁻¹) •
          openFormsMap (cU S') (f ≫ sX) p (ratForm ((cU S').ι ≫ f ≫ sX) p O
          ((((cU S').ι ≫ f ≫ sX).relativeDifferentialForms (p : ℤ)).presheaf.map
            (homOfLE hO).op ω))) ∈
      maximalIdeal E.localRing •
        wedgeSpan E.localRing (logLattice k E.localRing (L := X.functionField)) p := by
  classical
  have hηW : E.genericPoint ∈ (W₂ : X.Opens) := E.genericPoint_mem_of_nonempty hEW
  subst hk₀
  let := MMP.Mori.stalkAlgebra sX (j k₀).genericPoint
  let := MMP.Mori.functionFieldAlgebra sX
  let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
  let := MMP.Mori.functionFieldMapAlgebra f
  have := MMP.Mori.isScalarTower_functionFieldMap sX f
  have := MMP.Mori.isScalarTower_stalk_functionField sX (j k₀).genericPoint
  have := finiteDimensional_functionFieldMap f
  have := isSeparable_functionFieldMap sX f
  have hτu : ∀ k, k ≠ k₀ → IsUnit (X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW (τ k)) :=
    fun k hk => isUnit_germ_of_notMem_support (j k) W₂ (hτ k) hηW fun h =>
      hk (hjinj (eq_of_genericPoint_mem_support h).symm)
  have hvu : IsUnit (X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW v) := hv.map _
  have ht := maximalIdeal_localRing_eq_span (j k₀) W₂ hηW (hτ k₀)
  have htm : X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW (τ k₀) ∈
      maximalIdeal (j k₀).localRing := ht ▸ Ideal.mem_span_singleton_self _
  have := (j k₀).isDiscreteValuationRing_localRing
  have ht0 : X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW (τ k₀) ≠ 0 := by
    intro h0
    rw [h0, Set.singleton_zero, Ideal.span_zero] at ht
    exact IsDiscreteValuationRing.not_a_field _ ht
  set τ' : Fin r → (j k₀).localRing := fun k =>
    X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW (τ k)
  set T : Finset (Fin r) := Finset.univ.filter fun k => j k ∈ S.support
  have hk₀T : k₀ ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ _, hES⟩
  obtain ⟨a₀, ha₀⟩ := pow_mul_inv_mem_range_of_mem (K := X.functionField) hvu ht0 rfl hτu b hb
    hk₀T N
  set H : X.functionField := algebraMap (j k₀).localRing X.functionField (∏ k ∈ T, τ' k)
  have hH0 : H ≠ 0 := by
    refine fun h0 => ?_
    have h1 : (∏ k ∈ T, τ' k) = 0 :=
      IsFractionRing.injective (j k₀).localRing X.functionField (h0.trans (map_zero _).symm)
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h1
    by_cases hkk : k = k₀
    · subst hkk; exact ht0 hk
    · exact (hτu k hkk).ne_zero hk
  have hden : X.germToFunctionField (W₂ : X.Opens) (v * ∏ k, τ k ^ b k) =
      algebraMap (j k₀).localRing X.functionField
        (zDenom (X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW v) τ' b ∅ N) := by
    rw [zDenom, Finset.prod_empty, one_pow, mul_one, ← Scheme.algebraMap_germ_eq_germToFunctionField
      (X := X) hηW]
    simp only [τ', map_mul, map_prod, map_pow]
  have hdenT : zDenom (X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW v) τ' b T N =
      zDenom (X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW v) τ' b ∅ N *
        (∏ k ∈ T, τ' k) ^ N := by
    simp only [zDenom, Finset.prod_empty, one_pow, mul_one]
  have htK : X.germToFunctionField (W₂ : X.Opens) (τ k₀) = algebraMap (j k₀).localRing
      X.functionField (X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW (τ k₀)) :=
    (Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hηW _).symm
  set lam := z * (AlgebraicGeometry.functionFieldMap f G)⁻¹
  have hlamN : lam ^ N = AlgebraicGeometry.functionFieldMap f (algebraMap (j k₀).localRing
      X.functionField (zDenom (X.presheaf.germ (W₂ : X.Opens) (j k₀).genericPoint hηW v)
        τ' b ∅ N))⁻¹ := by
    rw [mul_pow, inv_pow, hz, ← map_pow, hG, hden, map_mul, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ ((map_ne_zero _).2 hψK), one_mul, map_inv₀]
  have hlam1N :
      (AlgebraicGeometry.functionFieldMap f (X.germToFunctionField (W₂ : X.Opens) (τ k₀)) *
      (lam * (AlgebraicGeometry.functionFieldMap f H)⁻¹)) ^ N =
      AlgebraicGeometry.functionFieldMap f (algebraMap (j k₀).localRing X.functionField a₀) := by
    rw [ha₀, mul_pow, mul_pow, inv_pow, hlamN, htK, hdenT]
    simp only [H, map_mul, map_inv₀, map_pow]
    ring
  have hmem := formsTrace_smul_mem_wedgeSpan_logLattice_of_mem sX f n S' hS' p hω O hO (j k₀)
    hW₀ W₂ hηW (τ k₀) ht (fun y hy => ?_)
    (lam * (AlgebraicGeometry.functionFieldMap f H)⁻¹) (fun y hy => ?_)
  · have key : ∀ x : ⋀[Y.functionField]^p Ω[Y.functionField⁄k],
        formsTrace k X.functionField Y.functionField p (lam • x) =
          H • formsTrace k X.functionField Y.functionField p
            ((lam * (AlgebraicGeometry.functionFieldMap f H)⁻¹) • x) := by
      intro x
      rw [← (formsTrace k X.functionField Y.functionField p).map_smul,
        ← algebraMap_smul Y.functionField H, smul_smul]
      congr 2
      change lam = AlgebraicGeometry.functionFieldMap f H *
        (lam * (AlgebraicGeometry.functionFieldMap f H)⁻¹)
      rw [mul_comm lam, ← mul_assoc, mul_inv_cancel₀ ((map_ne_zero _).2 hH0), one_mul]
    have heq := key (openFormsMap (cU S') (f ≫ sX) p (ratForm ((cU S').ι ≫ f ≫ sX) p O
      ((((cU S').ι ≫ f ≫ sX).relativeDifferentialForms (p : ℤ)).presheaf.map (homOfLE hO).op ω)))
    rw [heq, algebraMap_smul]
    refine Submodule.smul_mem_smul ?_ hmem
    rw [← Finset.mul_prod_erase T _ hk₀T]
    exact Ideal.mul_mem_right _ _ htm
  · obtain ⟨E', rfl⟩ := exists_primeDivisor_genericPoint_eq_of_map_eq f (j k₀) hy
    exact ⟨E', mem_support_of_map_genericPoint_eq f hS'def hES hy, rfl⟩
  · obtain ⟨r', hr', -⟩ := exists_stalk_eq_of_pow_eq_functionFieldMap f hy hN hlam1N
    exact ⟨r', hr'⟩

end MMP.FourfoldProofs.FractionalLogComplexProof
