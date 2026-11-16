module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.PullbackMap.Defs
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.PullbackMap.PrimeDivisor
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.PullbackMap.Gluing

/-!
# The pull-back into the logarithmic complex of the cover

Let `π : V ⟶ Spec ℂ` be smooth and integral, `D = S + Supp Bn` a relative simple normal crossing
divisor with `S ≥ 0` and `0 ≤ Bn < N`, `N M = Bn + div ψ`, and `g : V' ⟶ V` a finite surjective
cover by a smooth normal integral scheme on which the reduced inverse image `S'` of `S` is a
relative simple normal crossing divisor and `z^N = g^*ψ`. Then `θ ↦ g^*θ / z` carries the
sections of `C^p = 𝒪_V(-M) · Ω^p_V(log D)(-S)` over `W` to sections of `Ω^p_{V'}(log S')(-S')`
over `g⁻¹ W`: this is `MMP.FourfoldProofs.FractionalLogComplexProof.IMapSpec`.

The rational form `z⁻¹ g^*ρ` of the pull-back lies, at every prime divisor `E'` of `V'` over `W`,
in the wedges of the regular lattice of `𝒪_{V',E'}`, and, along `S'`, in the maximal ideal times
the wedges of the logarithmic lattice
(`MMP.FourfoldProofs.FractionalLogComplexProof.mem_lattices_of_cover`); it is therefore the rational
form of a section of `Ω^p_{V'}(log S')(-S')` over `g⁻¹ W`
(`MMP.FourfoldProofs.FractionalLogComplexProof.exists_relativeLogForm_of_forall_primeDivisor`).

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_section_eq_ratRes`: `ψ` restricts to
  a regular function on `V ∖ (D ∪ Supp M)`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.iMapSpec_of_cover`: the pull-back lands in
  `Ω^p_{V'}(log S')(-S')`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.67
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

/-- **`ψ` is a function on `U' = V ∖ (D ∪ Supp M)`.** If `N M = Bn + div ψ` with `Bn` supported on
`D`, then `ψ` has no zeros or poles on `U'`, so it is a regular function there. -/
theorem exists_section_eq_ratRes {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (D M Bn : MMP.Mori.Divisor X) (N : ℕ)
    (ψ : (MMP.Mori.RationalFunctions X)ˣ)
    (hψ : (N : ℤ) • M = Bn + MMP.Mori.principalDivisor ψ)
    (hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support) :
    ∃ uu : Γ(X, cU' D M),
      (MMP.Mori.toRationalFunctionsPresheaf X).app (op (cU' D M)) uu = ratRes (cU' D M) ψ := by
  refine MMP.Mori.Divisor.IsDivisorialSection.exists_eq fun E hE => Or.inr ?_
  obtain ⟨y, hyE, hyU⟩ := hE
  have hM : M E = 0 := by
    by_contra h
    exact hyU (Or.inr (MMP.Mori.DivisorWithCoeffs.support_subset_supp h hyE))
  have hB : Bn E = 0 := by
    by_contra h
    exact hyU (Or.inl (MMP.Mori.DivisorWithCoeffs.support_subset_supp
      (Finsupp.mem_support_iff.1 (hBD E h)) hyE))
  have hord : E.ord ψ = 0 := by
    have h := congrArg (fun F => F E) hψ
    simp only [Finsupp.smul_apply, Finsupp.add_apply, hM, hB, smul_zero, zero_add] at h
    rw [← MMP.Mori.coeff_principalDivisor]
    exact h.symm
  have hv := E.valuation_component ψ
  rw [hord] at hv
  rw [MMP.Mori.DivisorWithCoeffs.coeff_zero, neg_zero]
  exact hv.ge

open scoped Classical in
/-- **The pull-back `θ ↦ g^*θ / z` lands in `Ω^p_{V'}(log S')(-S')`.** For the cover of
`MMP.FourfoldProofs.FractionalLogComplexProof.CoverDatum`, the pull-back of a section of the fractional
logarithmic complex `C^p` over `W`, divided by the `N`-th root `z` of `g^*ψ`, extends to a section
of `Ω^p_{V'}(log S')(-S')` over `g⁻¹ W`. -/
theorem iMapSpec_of_cover (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [CompactSpace V] (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π)
    (S Bn : MMP.Mori.Divisor V) (hS : 0 ≤ S) (hSB : ∀ E, D E = S E + if Bn E = 0 then 0 else 1)
    (N : ℕ) (hN : 0 < N) (hB : ∀ E, 0 ≤ Bn E ∧ Bn E < N)
    (M : MMP.Mori.Divisor V) (ψ : (MMP.Mori.RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + MMP.Mori.principalDivisor ψ) [Nonempty (cU D)]
    {V' : Scheme.{0}} (g : V' ⟶ V) [Surjective g] [IsIntegral V']
    [SmoothOfRelativeDimension n (g ≫ π)] [IsLocallyNoetherian V'] [IsNormal V']
    (S' : MMP.Mori.Divisor V') (hS' : S'.IsRelativeSNC n (g ≫ π)) [Nonempty (cU S')]
    (hS'S : ∀ E' : MMP.Mori.PrimeDivisor V', S' E' =
      if ∃ E ∈ S.support, g E'.genericPoint = E.genericPoint then 1 else 0)
    (z : V'.functionField)
    (hz : z ^ N = AlgebraicGeometry.functionFieldMap g
      (MMP.Mori.rationalFunctionsEquivFunctionField V ψ)) :
    IMapSpec n π D hD S M g S' hS' z := by
  have hBn : ∀ E, 0 ≤ Bn E := fun E => (hB E).1
  have hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support := by
    intro E hE
    have hSE : 0 ≤ S E := Finsupp.le_def.1 hS E
    rw [Finsupp.mem_support_iff, hSB E, ite_eq_right hE]
    omega
  have : Smooth π := SmoothOfRelativeDimension.smooth n π
  have hsm : MMP.Mori.IsSmoothScheme π := (MMP.Mori.isSmoothScheme_iff π).2 this
  have hMC : M.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm M
  obtain ⟨uu, hu⟩ := exists_section_eq_ratRes D M Bn N ψ hψ hBD
  unfold IMapSpec
  intro p W θ hθ
  by_cases hne : ∃ O : (cU D).toScheme.affineOpens,
      (O : (cU D).toScheme.Opens) ≤ OO D M W ∧ Nonempty (O : (cU D).toScheme.Opens)
  swap
  · exact ⟨0, G1.zero_mem_relativeLogForms n (g ≫ π) S' hS' _ _ _,
      fun O hO hOne => (hne ⟨O, hO, hOne⟩).elim⟩
  obtain ⟨O₀, hO₀, hne₀⟩ := hne
  obtain ⟨ρ, hρ⟩ := exists_forall_openFormsMap_ratForm_eq π D M p W θ O₀ hO₀
  obtain ⟨θ', hθ'mem, hθ'⟩ := exists_relativeLogForm_of_forall_primeDivisor n (g ≫ π) S' hS' p
    (g ⁻¹ᵁ W)
    (letI := MMP.Mori.functionFieldAlgebra π
     letI := MMP.Mori.functionFieldAlgebra (g ≫ π)
     letI := MMP.Mori.functionFieldMapAlgebra g
     haveI := MMP.Mori.isScalarTower_functionFieldMap π g
     z⁻¹ • KaehlerDifferential.mapExteriorPower ℂ V.functionField V'.functionField p ρ)
    fun E hE => by
      have hEW : g E.genericPoint ∈ W := E.genericPoint_mem_of_nonempty hE
      obtain ⟨h1, h2⟩ := mem_lattices_of_cover n π D hD S Bn hSB N hN hBn hBD M uu hMC ψ hψ hu g
        z hz p W θ hθ ρ hρ E hEW
      refine ⟨h1, fun hES => h2 ?_⟩
      by_contra hno
      have h0 := hS'S E
      rw [ite_eq_right hno] at h0
      exact Finsupp.mem_support_iff.1 hES h0
  refine ⟨θ', hθ'mem, fun O hO _ O' hO' _ => ?_⟩
  rw [hθ' O' hO', hρ O hO]

end MMP.FourfoldProofs.FractionalLogComplexProof
