module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Retract.Basic
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.CyclicCoverExists
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.TraceMap.Basic
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.RationalIdentities

/-!
# Models of the fractional logarithmic complex of an integral variety are retracts

Let `π : V ⟶ Spec ℂ` be smooth projective with `V` integral, and carry the data of the fractional
logarithmic complex `C^• = 𝒪_V(-M) · Ω^•_V(log D)(-S)`. For the finite cover `g : V' ⟶ V` of
`MMP.FourfoldProofs.FractionalLogComplexProof.exists_coverDatum`, every model of `C^•` is a retract of
`g_* Ω^•_{V'}(log S')(-S')` in the category of complexes of sheaves of `π⁻¹𝒪`-modules, through
`θ ↦ g^*θ / z` and `ω' ↦ [k(V') : k(V)]⁻¹ Tr(z ω')`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.retract_of_isIntegral`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open scoped Classical in
/-- **Every model of `C^•` on an integral variety is a retract** of the direct image of the
twisted logarithmic de Rham complex of a smooth projective finite cover. -/
theorem retract_of_isIntegral (n : ℕ) {V : Scheme.{0}}
    (π : V ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension n π] (hπ : IsProjective π)
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S Bn : MMP.Mori.Divisor V)
    (hS : 0 ≤ S) (hSB : ∀ E, D E = S E + if Bn E = 0 then 0 else 1)
    (N : ℕ) (hN : 0 < N) (hB : ∀ E, 0 ≤ Bn E ∧ Bn E < N)
    (M : MMP.Mori.Divisor V) (ψ : (MMP.Mori.RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + MMP.Mori.principalDivisor ψ) (u : Γ(V, cU' D M))
    (hu : (MMP.Mori.toRationalFunctionsPresheaf V).app (op (cU' D M)) u = ratRes (cU' D M) ψ)
    (K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ)
    (F : ℕ → V.Modules)
    (e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p))
    (ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M W)))
    (hK : IsCModel n π D hD S M N u K F e ι) :
    ∃ (V' : Scheme.{0}) (g : V' ⟶ V) (_ : IsFinite g) (_ : SmoothOfRelativeDimension n (g ≫ π))
      (S' : MMP.Mori.Divisor V') (hS' : S'.IsRelativeSNC n (g ≫ π)),
      IsProjective (g ≫ π) ∧
      ∃ (a : K ⟶ ((relDirectImage g π).mapHomologicalComplex _).obj
          (MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ π) S' hS' S'.suppIdeal))
        (r : ((relDirectImage g π).mapHomologicalComplex _).obj
          (MMP.Mori.Divisor.relativeLogDeRhamComplex n (g ≫ π) S' hS' S'.suppIdeal) ⟶ K),
        a ≫ r = 𝟙 K := by
  have : Nonempty (cU D) := ⟨⟨genericPoint V, MMP.Fourfold.genericPoint_notMem_supp D⟩⟩
  have : Nonempty (cU' D M) := ⟨⟨genericPoint V, genericPoint_mem_cU' D M⟩⟩
  obtain ⟨V', g, hfin, _, _, hsm, hπ', _, _, _, S', hS', hS'S, z, hz⟩ :=
    exists_coverDatum n π hπ D hD S Bn hS hSB N hN M ψ hψ
  have : Nonempty (cU S') := ⟨⟨genericPoint V', MMP.Fourfold.genericPoint_notMem_supp S'⟩⟩
  set ψK := MMP.Mori.rationalFunctionsEquivFunctionField V ψ
  have hψK : ψK ≠ 0 := (ψ.isUnit.map (MMP.Mori.rationalFunctionsEquivFunctionField V)).ne_zero
  have hgerm : V.germToFunctionField (cU' D M) u = ψK :=
    (rationalFunctionsEquivFunctionField_eq_germ (U := cU' D M) (ψ : _) u hu).symm
  let := MMP.Mori.functionFieldAlgebra π
  let := MMP.Mori.functionFieldAlgebra (g ≫ π)
  let := MMP.Mori.functionFieldMapAlgebra g
  have := MMP.Mori.isScalarTower_functionFieldMap π g
  have := finiteDimensional_functionFieldMap g
  have := isSeparable_functionFieldMap π g
  obtain ⟨a, r, har⟩ := retract_of_cover n π D hD S M N u ψK g S' hS' z hgerm
    (iMapSpec_of_cover n π D hD S Bn hS hSB N hN hB M ψ hψ g S' hS' hS'S z hz)
    (rMapSpec_of_cover n π D hD S Bn hS hSB N hN hB M ψ hψ g S' hS' hS'S z hz)
    (ratCompat_of_pow_eq (k := ℂ) (by omega) hψK hz) K F e ι hK
  exact ⟨V', g, hfin, hsm, S', hS', hπ', a, r, har⟩

end MMP.FourfoldProofs.FractionalLogComplexProof
