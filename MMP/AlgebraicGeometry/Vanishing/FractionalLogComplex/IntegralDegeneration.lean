module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.CyclicCoverExists
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.TraceMap.Basic
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.RationalIdentities

/-!
# Degeneration of the fractional logarithmic complex of an integral variety

Let `π : V ⟶ Spec ℂ` be smooth projective with `V` integral, and carry the data of the fractional
logarithmic complex `C^• = 𝒪_V(-M) · Ω^•_V(log D)(-S)`. A finite cover `g : V' ⟶ V` by a smooth
projective integral `V'` on which the reduced inverse image `S'` of `S` is a relative simple
normal crossing divisor and `g^*ψ = z^N` exists
(`MMP.FourfoldProofs.FractionalLogComplexProof.exists_coverDatum`). The pull-back
`θ ↦ g^*θ / z` and the trace `ω' ↦ [k(V') : k(V)]⁻¹ Tr(z ω')` exhibit every model of `C^•` as a
retract of `g_* Ω^•_{V'}(log S')(-S')`, so it is `E₁`-degenerate when the retract argument
`MMP.FourfoldProofs.FractionalLogComplexProof.RetractSpec` holds.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.fracDegeneration_of_isIntegral`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open scoped Classical in
/-- **Degeneration for an integral variety.** The fractional logarithmic complex of `D`, `S`, `M`
and `N` satisfies `FracDegeneration`, provided the retract argument `RetractSpec` holds for every
finite surjective cover `g : V' ⟶ V` by a smooth integral `V'` with a relative SNC divisor `S'`. -/
theorem fracDegeneration_of_isIntegral (n : ℕ) {V : Scheme.{0}}
    (π : V ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension n π] (hπ : IsProjective π)
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (S Bn : MMP.Mori.Divisor V)
    (hS : 0 ≤ S) (hSB : ∀ E, D E = S E + if Bn E = 0 then 0 else 1)
    (N : ℕ) (hN : 0 < N) (hB : ∀ E, 0 ≤ Bn E ∧ Bn E < N)
    (M : MMP.Mori.Divisor V) (ψ : (MMP.Mori.RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + MMP.Mori.principalDivisor ψ) (u : Γ(V, cU' D M))
    (hu : (MMP.Mori.toRationalFunctionsPresheaf V).app (op (cU' D M)) u = ratRes (cU' D M) ψ)
    (hR : ∀ [Nonempty (cU D)] [Nonempty (cU' D M)] {V' : Scheme.{0}} (g : V' ⟶ V)
      [IsFinite g] [Surjective g] [IsIntegral V'] [SmoothOfRelativeDimension n (g ≫ π)]
      [IsLocallyNoetherian V'] [IsNormal V'] [CompactSpace V']
      (S' : MMP.Mori.Divisor V') (hS' : S'.IsRelativeSNC n (g ≫ π)) [Nonempty (cU S')]
      (z : V'.functionField),
      RetractSpec n π D hD S M N u (MMP.Mori.rationalFunctionsEquivFunctionField V ψ) g S' hS'
        z) :
    FracDegeneration n π D hD S M N u := by
  have : Nonempty (cU D) := ⟨⟨genericPoint V, MMP.Fourfold.genericPoint_notMem_supp D⟩⟩
  have : Nonempty (cU' D M) := ⟨⟨genericPoint V, genericPoint_mem_cU' D M⟩⟩
  obtain ⟨V', g, _, _, _, _, hπ', _, _, _, S', hS', hS'S, z, hz⟩ :=
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
  exact hR g S' hS' z hπ hπ' hgerm
    (iMapSpec_of_cover n π D hD S Bn hS hSB N hN hB M ψ hψ g S' hS' hS'S z hz)
    (rMapSpec_of_cover n π D hD S Bn hS hSB N hN hB M ψ hψ g S' hS' hS'S z hz)
    (ratCompat_of_pow_eq (k := ℂ) (by omega) hψK hz)

end MMP.FourfoldProofs.FractionalLogComplexProof
