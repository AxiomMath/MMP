module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.TraceMap.FormsTraceLattice
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Place.LogFormLattice

/-!
# The trace of a logarithmic form of the cover at a prime divisor

Let `f : Y ⟶ X` be a finite surjective morphism of normal integral schemes, both smooth of
relative dimension `n` over a field `k` of characteristic zero, `S'` a relative simple normal
crossing divisor on `Y`, and `ω'` a section of `Ω^p_Y(log S')(-S')` over an open containing the
points over the generic point of a prime divisor `E` of `X`, with uniformizer `t`. Let `λ` be a
rational function of `Y`.

* If no point over `E` lies on `S'` and `λ` is regular at the points over `E`, the trace of
  `λ ω'` lies in the wedges of the regular lattice of `𝒪_{X,E}`.
* If no point over `E` lies on `S'` and `t λ` lies in the maximal ideal at the points over `E`,
  the trace lies in the wedges of the logarithmic lattice.
* If every point over `E` is the generic point of a component of `S'` and `t λ` is regular at
  those points, the trace lies in the wedges of the logarithmic lattice.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_smul_mem_wedgeSpan_regLattice`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_smul_mem_wedgeSpan_logLattice_of_notMem`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_smul_mem_wedgeSpan_logLattice_of_mem`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing KaehlerDifferential

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y] [IsFinite f] [Surjective f]
  [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]

/-- If no point of `Y` over the generic point of `E` lies on `S'` and `lam` is regular at every
such point, then the trace of `lam • ω` lies in the `p`-th wedges of the regular lattice of
`𝒪_{X,E}`. -/
theorem formsTrace_smul_mem_wedgeSpan_regLattice (n : ℕ) [SmoothOfRelativeDimension n sX]
    [SmoothOfRelativeDimension n (f ≫ sX)] (S' : MMP.Mori.Divisor Y)
    (hS' : S'.IsRelativeSNC n (f ≫ sX)) [Nonempty (cU S')] (p : ℕ) {W₀ : Y.Opens}
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU S').ι ≫ f ≫ sX)).piece
      (p : ℤ)).val.obj (op ((cU S').ι ⁻¹ᵁ W₀))}
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n (f ≫ sX) S' hS' S'.suppIdeal p W₀)
    (O : (cU S').toScheme.affineOpens) (hO : (O : (cU S').toScheme.Opens) ≤ (cU S').ι ⁻¹ᵁ W₀)
    [Nonempty (O : (cU S').toScheme.Opens)] (E : MMP.Mori.PrimeDivisor X)
    (hW₀ : ∀ y : Y, f y = E.genericPoint → y ∈ W₀)
    (hS'E : ∀ y : Y, f y = E.genericPoint → ∀ F ∈ S'.support, y ∉ F.support)
    (lam : Y.functionField)
    (hlam : ∀ y : Y, f y = E.genericPoint →
      lam ∈ (algebraMap (Y.presheaf.stalk y) Y.functionField).range) :
    letI := MMP.Mori.stalkAlgebra sX E.genericPoint
    letI := MMP.Mori.functionFieldAlgebra sX
    letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    letI := MMP.Mori.functionFieldMapAlgebra f
    haveI := MMP.Mori.isScalarTower_functionFieldMap sX f
    haveI := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
    haveI := finiteDimensional_functionFieldMap f
    haveI := isSeparable_functionFieldMap sX f
    formsTrace k X.functionField Y.functionField p
        (lam • openFormsMap (cU S') (f ≫ sX) p (ratForm ((cU S').ι ≫ f ≫ sX) p O
          ((((cU S').ι ≫ f ≫ sX).relativeDifferentialForms (p : ℤ)).presheaf.map
            (homOfLE hO).op ω))) ∈
      wedgeSpan E.localRing (regLattice k E.localRing (L := X.functionField)) p := by
  classical
  let := MMP.Mori.stalkAlgebra sX E.genericPoint
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  have := essFiniteType_stalkAlgebra sX E.genericPoint
  obtain ⟨hfsA, hfreeA, hfinA⟩ := formallySmooth_free_finite_stalk sX (m := n) E.genericPoint
  have := E.isDiscreteValuationRing_localRing
  -- a uniformizer of `𝒪_{X,E}` from a section on an affine open
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  obtain ⟨U₀, hηU₀, a₀, ha₀⟩ := X.presheaf.exists_germ_eq (x := E.genericPoint) ϖ
  obtain ⟨W, hηW, hWU⟩ := G1.exists_affineOpens_le (X := X) hηU₀
  set t : Γ(X, W) := X.presheaf.map (homOfLE hWU).op a₀
  have htϖ : X.presheaf.germ (W : X.Opens) E.genericPoint hηW t = ϖ := by
    rw [TopCat.Presheaf.germ_res_apply]
    exact ha₀
  have ht : maximalIdeal E.localRing =
      Ideal.span {X.presheaf.germ (W : X.Opens) E.genericPoint hηW t} := by
    rw [htϖ]
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have ht0 : X.presheaf.germ (W : X.Opens) E.genericPoint hηW t ≠ 0 := by
    rw [htϖ]; exact hϖ.ne_zero
  have htK : algebraMap E.localRing X.functionField
      (X.presheaf.germ (W : X.Opens) E.genericPoint hηW t) ≠ 0 := fun h0 =>
    ht0 (IsFractionRing.injective E.localRing X.functionField (h0.trans (map_zero _).symm))
  -- an adapted basis at `E`
  let b₀ := Module.Free.chooseBasis E.localRing Ω[E.localRing⁄k]
  obtain ⟨m, x, bA, hbA⟩ := exists_basis_D_cons k b₀ ht ht0
  let := MMP.Mori.functionFieldAlgebra sX
  let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
  let := MMP.Mori.functionFieldMapAlgebra f
  have := MMP.Mori.isScalarTower_functionFieldMap sX f
  have := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
  have := finiteDimensional_functionFieldMap f
  have := isSeparable_functionFieldMap sX f
  refine formsTrace_mem_wedgeSpan_regLattice sX f E W hηW t ht x bA hbA htK p _ fun y hy => ?_
  let := MMP.Mori.stalkAlgebra (f ≫ sX) y
  have := MMP.Mori.isScalarTower_stalk_functionField (f ≫ sX) y
  have := isDiscreteValuationRing_stalk_of_map_eq_genericPoint f E hy
  obtain ⟨σ, hσ⟩ := IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk y)
  obtain ⟨m', -, yv, bR, hbR, hmem⟩ := exists_adapted_mem_wedgeSpan_regular n (f ≫ sX) S' hS'
    S'.suppIdeal p hω O hO (hW₀ y hy) (hS'E y hy)
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer σ).1 hσ) hσ.ne_zero
  -- the two adapted bases have the same size
  have hmm : m' = m := by
    have := Fintype.card_congr ((pullbackBasis (L := Y.functionField)
      (regBasis k (K := X.functionField) bA)).indexEquiv (regBasis k (K := Y.functionField) bR))
    simpa using this.symm
  subst hmm
  obtain ⟨ρ, hρ⟩ := hlam y hy
  refine ⟨σ, (IsDiscreteValuationRing.irreducible_iff_uniformizer σ).1 hσ, yv, bR, hbR, ρ, _,
    hmem, ?_⟩
  rw [hρ]

/-- If no point of `Y` over the generic point of `E` lies on `S'` and `t * lam` lies in the
maximal ideal of the stalk at every such point, where `t` is a uniformizer of `𝒪_{X,E}`, then the
trace of `lam • ω` lies in the `p`-th wedges of the logarithmic lattice of `𝒪_{X,E}`. -/
theorem formsTrace_smul_mem_wedgeSpan_logLattice_of_notMem (n : ℕ) [SmoothOfRelativeDimension n sX]
    [SmoothOfRelativeDimension n (f ≫ sX)] (S' : MMP.Mori.Divisor Y)
    (hS' : S'.IsRelativeSNC n (f ≫ sX)) [Nonempty (cU S')] (p : ℕ) {W₀ : Y.Opens}
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU S').ι ≫ f ≫ sX)).piece
      (p : ℤ)).val.obj (op ((cU S').ι ⁻¹ᵁ W₀))}
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n (f ≫ sX) S' hS' S'.suppIdeal p W₀)
    (O : (cU S').toScheme.affineOpens) (hO : (O : (cU S').toScheme.Opens) ≤ (cU S').ι ⁻¹ᵁ W₀)
    [Nonempty (O : (cU S').toScheme.Opens)] (E : MMP.Mori.PrimeDivisor X)
    (hW₀ : ∀ y : Y, f y = E.genericPoint → y ∈ W₀)
    (W : X.affineOpens) (hηW : E.genericPoint ∈ (W : X.Opens)) (t : Γ(X, W))
    (ht : maximalIdeal E.localRing =
      Ideal.span {X.presheaf.germ (W : X.Opens) E.genericPoint hηW t})
    (hS'E : ∀ y : Y, f y = E.genericPoint → ∀ F ∈ S'.support, y ∉ F.support)
    (lam : Y.functionField)
    (hlam : ∀ y : Y, f y = E.genericPoint →
      haveI : Nonempty (W : X.Opens) := ⟨⟨_, hηW⟩⟩
      ∃ r ∈ maximalIdeal (Y.presheaf.stalk y), algebraMap (Y.presheaf.stalk y) Y.functionField r =
        AlgebraicGeometry.functionFieldMap f (X.germToFunctionField (W : X.Opens) t) * lam) :
    letI := MMP.Mori.stalkAlgebra sX E.genericPoint
    letI := MMP.Mori.functionFieldAlgebra sX
    letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    letI := MMP.Mori.functionFieldMapAlgebra f
    haveI := MMP.Mori.isScalarTower_functionFieldMap sX f
    haveI := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
    haveI := finiteDimensional_functionFieldMap f
    haveI := isSeparable_functionFieldMap sX f
    formsTrace k X.functionField Y.functionField p
        (lam • openFormsMap (cU S') (f ≫ sX) p (ratForm ((cU S').ι ≫ f ≫ sX) p O
          ((((cU S').ι ≫ f ≫ sX).relativeDifferentialForms (p : ℤ)).presheaf.map
            (homOfLE hO).op ω))) ∈
      wedgeSpan E.localRing (logLattice k E.localRing (L := X.functionField)) p := by
  classical
  have : Nonempty (W : X.Opens) := ⟨⟨_, hηW⟩⟩
  let := MMP.Mori.stalkAlgebra sX E.genericPoint
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  have := essFiniteType_stalkAlgebra sX E.genericPoint
  obtain ⟨hfsA, hfreeA, hfinA⟩ := formallySmooth_free_finite_stalk sX (m := n) E.genericPoint
  have := E.isDiscreteValuationRing_localRing
  have ht0 : X.presheaf.germ (W : X.Opens) E.genericPoint hηW t ≠ 0 := by
    intro h0
    rw [h0, Set.singleton_zero, Ideal.span_zero] at ht
    exact IsDiscreteValuationRing.not_a_field E.localRing ht
  have htK : algebraMap E.localRing X.functionField
      (X.presheaf.germ (W : X.Opens) E.genericPoint hηW t) ≠ 0 := fun h0 =>
    ht0 (IsFractionRing.injective E.localRing X.functionField (h0.trans (map_zero _).symm))
  let b₀ := Module.Free.chooseBasis E.localRing Ω[E.localRing⁄k]
  obtain ⟨m, x, bA, hbA⟩ := exists_basis_D_cons k b₀ ht ht0
  let := MMP.Mori.functionFieldAlgebra sX
  let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
  let := MMP.Mori.functionFieldMapAlgebra f
  have := MMP.Mori.isScalarTower_functionFieldMap sX f
  have := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
  have := finiteDimensional_functionFieldMap f
  have := isSeparable_functionFieldMap sX f
  refine formsTrace_mem_wedgeSpan_logLattice sX f E W hηW t ht x bA hbA htK p _ fun y hy => ?_
  let := MMP.Mori.stalkAlgebra (f ≫ sX) y
  have := MMP.Mori.isScalarTower_stalk_functionField (f ≫ sX) y
  have := isDiscreteValuationRing_stalk_of_map_eq_genericPoint f E hy
  obtain ⟨σ, hσ⟩ := IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk y)
  have hσm := (IsDiscreteValuationRing.irreducible_iff_uniformizer σ).1 hσ
  obtain ⟨m', -, yv, bR, hbR, hmem⟩ := exists_adapted_mem_wedgeSpan_regular n (f ≫ sX) S' hS'
    S'.suppIdeal p hω O hO (hW₀ y hy) (hS'E y hy) hσm hσ.ne_zero
  have hmm : m' = m := by
    have := Fintype.card_congr ((pullbackBasis (L := Y.functionField)
      (regBasis k (K := X.functionField) bA)).indexEquiv (regBasis k (K := Y.functionField) bR))
    simpa using this.symm
  subst hmm
  obtain ⟨r, hr, hr'⟩ := hlam y hy
  have hσL : algebraMap (Y.presheaf.stalk y) Y.functionField σ ≠ 0 := fun h0 =>
    hσ.ne_zero (IsFractionRing.injective _ Y.functionField (h0.trans (map_zero _).symm))
  refine ⟨σ, hσm, yv, bR, hbR, r, hr, _, wedgeSpan_mono ?_ p hmem, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨j', rfl⟩
    refine Fin.cases ?_ (fun l => ?_) j'
    · simp only [Fin.cons_zero]
      have e : KaehlerDifferential.D k Y.functionField
          (algebraMap (Y.presheaf.stalk y) Y.functionField σ) =
          σ • ((algebraMap (Y.presheaf.stalk y) Y.functionField σ)⁻¹ •
            KaehlerDifferential.D k Y.functionField
              (algebraMap (Y.presheaf.stalk y) Y.functionField σ)) := by
        rw [← algebraMap_smul Y.functionField σ, smul_smul, mul_inv_cancel₀ hσL, one_smul]
      have h0 := Submodule.smul_mem (Submodule.span (Y.presheaf.stalk y) (Set.range (Fin.cons
          ((algebraMap (Y.presheaf.stalk y) Y.functionField σ)⁻¹ •
            KaehlerDifferential.D k Y.functionField
              (algebraMap (Y.presheaf.stalk y) Y.functionField σ))
          fun l => KaehlerDifferential.D k Y.functionField
            (algebraMap (Y.presheaf.stalk y) Y.functionField (yv l))
          : Fin (m' + 1) → Ω[Y.functionField⁄k]))) σ
        (Submodule.subset_span ⟨0, by rw [Fin.cons_zero]⟩)
      rwa [← e] at h0
    · simp only [Fin.cons_succ]
      exact Submodule.subset_span ⟨l.succ, by rw [Fin.cons_succ]⟩
  · rw [smul_smul, hr']

/-- For `ω` a twisted logarithmic form: if every point of `Y` over the generic point of `E` is the
generic point of a component of `S'` and `t * lam` is regular at each such point, where `t` is a
uniformizer of `𝒪_{X,E}`, then the trace of `lam • ω` lies in the `p`-th wedges of the
logarithmic lattice of `𝒪_{X,E}`. -/
theorem formsTrace_smul_mem_wedgeSpan_logLattice_of_mem (n : ℕ) [SmoothOfRelativeDimension n sX]
    [SmoothOfRelativeDimension n (f ≫ sX)] (S' : MMP.Mori.Divisor Y)
    (hS' : S'.IsRelativeSNC n (f ≫ sX)) [Nonempty (cU S')] (p : ℕ) {W₀ : Y.Opens}
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU S').ι ≫ f ≫ sX)).piece
      (p : ℤ)).val.obj (op ((cU S').ι ⁻¹ᵁ W₀))}
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n (f ≫ sX) S' hS' S'.suppIdeal p W₀)
    (O : (cU S').toScheme.affineOpens) (hO : (O : (cU S').toScheme.Opens) ≤ (cU S').ι ⁻¹ᵁ W₀)
    [Nonempty (O : (cU S').toScheme.Opens)] (E : MMP.Mori.PrimeDivisor X)
    (hW₀ : ∀ y : Y, f y = E.genericPoint → y ∈ W₀)
    (W : X.affineOpens) (hηW : E.genericPoint ∈ (W : X.Opens)) (t : Γ(X, W))
    (ht : maximalIdeal E.localRing =
      Ideal.span {X.presheaf.germ (W : X.Opens) E.genericPoint hηW t})
    (hS'E : ∀ y : Y, f y = E.genericPoint → ∃ E' ∈ S'.support, E'.genericPoint = y)
    (lam : Y.functionField)
    (hlam : ∀ y : Y, f y = E.genericPoint →
      haveI : Nonempty (W : X.Opens) := ⟨⟨_, hηW⟩⟩
      ∃ r : Y.presheaf.stalk y, algebraMap (Y.presheaf.stalk y) Y.functionField r =
        AlgebraicGeometry.functionFieldMap f (X.germToFunctionField (W : X.Opens) t) * lam) :
    letI := MMP.Mori.stalkAlgebra sX E.genericPoint
    letI := MMP.Mori.functionFieldAlgebra sX
    letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    letI := MMP.Mori.functionFieldMapAlgebra f
    haveI := MMP.Mori.isScalarTower_functionFieldMap sX f
    haveI := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
    haveI := finiteDimensional_functionFieldMap f
    haveI := isSeparable_functionFieldMap sX f
    formsTrace k X.functionField Y.functionField p
        (lam • openFormsMap (cU S') (f ≫ sX) p (ratForm ((cU S').ι ≫ f ≫ sX) p O
          ((((cU S').ι ≫ f ≫ sX).relativeDifferentialForms (p : ℤ)).presheaf.map
            (homOfLE hO).op ω))) ∈
      wedgeSpan E.localRing (logLattice k E.localRing (L := X.functionField)) p := by
  classical
  have : Nonempty (W : X.Opens) := ⟨⟨_, hηW⟩⟩
  let := MMP.Mori.stalkAlgebra sX E.genericPoint
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  have := essFiniteType_stalkAlgebra sX E.genericPoint
  obtain ⟨hfsA, hfreeA, hfinA⟩ := formallySmooth_free_finite_stalk sX (m := n) E.genericPoint
  have := E.isDiscreteValuationRing_localRing
  have ht0 : X.presheaf.germ (W : X.Opens) E.genericPoint hηW t ≠ 0 := by
    intro h0
    rw [h0, Set.singleton_zero, Ideal.span_zero] at ht
    exact IsDiscreteValuationRing.not_a_field E.localRing ht
  have htK : algebraMap E.localRing X.functionField
      (X.presheaf.germ (W : X.Opens) E.genericPoint hηW t) ≠ 0 := fun h0 =>
    ht0 (IsFractionRing.injective E.localRing X.functionField (h0.trans (map_zero _).symm))
  let b₀ := Module.Free.chooseBasis E.localRing Ω[E.localRing⁄k]
  obtain ⟨m, x, bA, hbA⟩ := exists_basis_D_cons k b₀ ht ht0
  let := MMP.Mori.functionFieldAlgebra sX
  let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
  let := MMP.Mori.functionFieldMapAlgebra f
  have := MMP.Mori.isScalarTower_functionFieldMap sX f
  have := MMP.Mori.isScalarTower_stalk_functionField sX E.genericPoint
  have := finiteDimensional_functionFieldMap f
  have := isSeparable_functionFieldMap sX f
  refine formsTrace_mem_wedgeSpan_logLattice sX f E W hηW t ht x bA hbA htK p _ fun y hy => ?_
  let := MMP.Mori.stalkAlgebra (f ≫ sX) y
  have := MMP.Mori.isScalarTower_stalk_functionField (f ≫ sX) y
  have := isDiscreteValuationRing_stalk_of_map_eq_genericPoint f E hy
  obtain ⟨E', hE', hyE'⟩ := hS'E y hy
  subst hyE'
  obtain ⟨σ, hσm, m', -, yv, bR, hbR, η, hη, heq⟩ := exists_adapted_eq_smul_log n (f ≫ sX) S'
    hS' p hω O hO hE' (hW₀ _ hy)
  have hmm : m' = m := by
    have := Fintype.card_congr ((pullbackBasis (L := Y.functionField)
      (regBasis k (K := X.functionField) bA)).indexEquiv (regBasis k (K := Y.functionField) bR))
    simpa using this.symm
  subst hmm
  obtain ⟨r, hr'⟩ := hlam _ hy
  have hσ : σ ∈ maximalIdeal (Y.presheaf.stalk E'.genericPoint) :=
    hσm ▸ Ideal.mem_span_singleton_self σ
  refine ⟨σ, hσm, yv, bR, hbR, r * σ, Ideal.mul_mem_left _ _ hσ, η, hη, ?_⟩
  rw [heq, smul_smul, smul_smul, map_mul, hr']

end MMP.FourfoldProofs.FractionalLogComplexProof
