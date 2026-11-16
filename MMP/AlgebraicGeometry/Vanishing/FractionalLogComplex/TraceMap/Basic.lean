module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Retract.Defs
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.PullbackMap.Basic
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.TraceMap.PrimeDivisor
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.TraceMap.LocalSections

/-!
# The trace map into the fractional logarithmic complex

Let `π : V ⟶ Spec ℂ` carry the data of the fractional logarithmic complex
`C^• = 𝒪_V(-M) · Ω^•_V(log D)(-S)`, and `g : V' ⟶ V` a finite surjective cover by an integral
smooth variety on which the reduced inverse image `S'` of `S` is a relative simple normal crossing
divisor and `z^N = g^*ψ`. For a section `ω'` of `Ω^p_{V'}(log S')(-S')` over `g⁻¹ W` the rational
form `ρ = [k(V') : k(V)]⁻¹ Tr(z ω')` is the rational form of a section of `C^p` over `W`. Near a
point of `W`, a local generator `g₀` of `𝒪_V(-M)` factors as `g₀^N = ψ v ∏ τₖ^{bₖ}`, and
`ρ / g₀ = [k(V') : k(V)]⁻¹ Tr((z / g^*g₀) ω')` lies, at every prime divisor `E`, in the wedges of
the regular lattice (`E ∉ D`), of the logarithmic lattice (`E ∈ D`), and in the maximal ideal
times the latter (`E ∈ S`); so `ρ` is locally `g₀ η` with `η` a section of `Ω^p_V(log D)(-S)`,
and these local sections glue.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.rMapSpec_of_cover`: the statement
  `MMP.FourfoldProofs.FractionalLogComplexProof.RMapSpec` for the cover.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

/-- Multiplication by the inverse of a natural number preserves a submodule over a ring
containing a field of characteristic zero. -/
theorem natCast_inv_smul_mem {k A K Mo : Type*} [Field k] [CharZero k] [CommSemiring A]
    [DivisionRing K] [Algebra k A] [Algebra A K] [Algebra k K] [IsScalarTower k A K]
    [AddCommMonoid Mo]
    [Module K Mo] [Module A Mo] [IsScalarTower A K Mo] {N : Submodule A Mo} (c : ℕ) {m : Mo}
    (hm : m ∈ N) : (c : K)⁻¹ • m ∈ N := by
  have e : (c : K)⁻¹ = algebraMap A K (algebraMap k A (c : k)⁻¹) := by
    rw [← IsScalarTower.algebraMap_apply, map_inv₀, map_natCast]
  rw [e, algebraMap_smul]
  exact N.smul_mem _ hm

open scoped Classical in
/-- **The trace map lands in `C^p`.** For a finite surjective cover `g : V' ⟶ V` on which `S'` is
the reduced relative SNC inverse image of `S`, and `z` with `z ^ N = g^* ψ`, `RMapSpec` holds. -/
theorem rMapSpec_of_cover (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [CompactSpace V] (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π)
    (S Bn : MMP.Mori.Divisor V) (hS : 0 ≤ S) (hSB : ∀ E, D E = S E + if Bn E = 0 then 0 else 1)
    (N : ℕ) (hN : 0 < N) (hB : ∀ E, 0 ≤ Bn E ∧ Bn E < N)
    (M : MMP.Mori.Divisor V) (ψ : (MMP.Mori.RationalFunctions V)ˣ)
    (hψ : (N : ℤ) • M = Bn + MMP.Mori.principalDivisor ψ) [Nonempty (cU D)]
    {V' : Scheme.{0}} (g : V' ⟶ V) [IsFinite g] [Surjective g] [IsIntegral V']
    [SmoothOfRelativeDimension n (g ≫ π)] [IsLocallyNoetherian V'] [IsNormal V']
    (S' : MMP.Mori.Divisor V') (hS' : S'.IsRelativeSNC n (g ≫ π)) [Nonempty (cU S')]
    (hS'S : ∀ E' : MMP.Mori.PrimeDivisor V', S' E' =
      if ∃ E ∈ S.support, g E'.genericPoint = E.genericPoint then 1 else 0)
    (z : V'.functionField)
    (hz : z ^ N = AlgebraicGeometry.functionFieldMap g
      (MMP.Mori.rationalFunctionsEquivFunctionField V ψ)) :
    RMapSpec n π D hD S M g S' hS' z := by
  classical
  have hBn : ∀ E, 0 ≤ Bn E := fun E => (hB E).1
  have hBD : ∀ E, Bn E ≠ 0 → E ∈ D.support := by
    intro E hE
    have hSE : 0 ≤ S E := Finsupp.le_def.1 hS E
    rw [Finsupp.mem_support_iff, hSB E, ite_eq_right hE]
    omega
  have hSD : ∀ E ∈ S.support, E ∈ D.support := by
    intro E hE
    have hSE : 0 ≤ S E := Finsupp.le_def.1 hS E
    rw [Finsupp.mem_support_iff] at hE ⊢
    rw [hSB E]
    split_ifs <;> omega
  have hN0 : N ≠ 0 := by omega
  have : Smooth π := SmoothOfRelativeDimension.smooth n π
  have hsm : MMP.Mori.IsSmoothScheme π := (MMP.Mori.isSmoothScheme_iff π).2 this
  have hMC : M.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm M
  obtain ⟨uu, hu⟩ := exists_section_eq_ratRes D M Bn N ψ hψ hBD
  set ψK := MMP.Mori.rationalFunctionsEquivFunctionField V ψ with hψKdef
  have hψK : ψK ≠ 0 := (ψ.isUnit.map (MMP.Mori.rationalFunctionsEquivFunctionField V)).ne_zero
  let := MMP.Mori.functionFieldAlgebra π
  let := MMP.Mori.functionFieldAlgebra (g ≫ π)
  let := MMP.Mori.functionFieldMapAlgebra g
  have := MMP.Mori.isScalarTower_functionFieldMap π g
  have := finiteDimensional_functionFieldMap g
  have := isSeparable_functionFieldMap π g
  unfold RMapSpec
  intro p W θ' hθ'
  by_cases hne : ∃ O' : (cU S').toScheme.affineOpens,
      (O' : (cU S').toScheme.Opens) ≤ (cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W) ∧
        Nonempty (O' : (cU S').toScheme.Opens)
  swap
  · exact ⟨0, Cond.zero n π D hD S M p W, fun _ _ _ O' hO' hO'ne => (hne ⟨O', hO', hO'ne⟩).elim⟩
  obtain ⟨O'₀, hO'₀, hne₀⟩ := hne
  set ω'₀ := openFormsMap (cU S') (g ≫ π) p (ratForm ((cU S').ι ≫ g ≫ π) p O'₀
    ((((cU S').ι ≫ g ≫ π).relativeDifferentialForms (p : ℤ)).presheaf.map
      (homOfLE hO'₀).op θ')) with hω'₀
  set c : ℕ := Module.finrank V.functionField V'.functionField
  set ρ := (c : V.functionField)⁻¹ • formsTrace ℂ V.functionField V'.functionField p (z • ω'₀)
    with hρ
  have hind : ∀ (O' : (cU S').toScheme.affineOpens)
      (hO' : (O' : (cU S').toScheme.Opens) ≤ (cU S').ι ⁻¹ᵁ (g ⁻¹ᵁ W))
      [Nonempty (O' : (cU S').toScheme.Opens)],
      openFormsMap (cU S') (g ≫ π) p (ratForm ((cU S').ι ≫ g ≫ π) p O'
        ((((cU S').ι ≫ g ≫ π).relativeDifferentialForms (p : ℤ)).presheaf.map
          (homOfLE hO').op θ')) = ω'₀ := by
    intro O' hO' _
    rw [ratForm_eq_of_le ((cU S').ι ≫ g ≫ π) p θ' hO' hO'₀]
  refine Exists.imp (fun θ hθ => ⟨hθ.1, fun O hO _ O' hO' _ => by rw [hθ.2 O hO, hind O' hO']⟩)
    (exists_cond_of_forall_localRep n π D hD S M p W ρ fun x hx => ?_)
  -- the factorization of a local generator of `𝒪_V(-M)` near `x`
  obtain ⟨W₂, hx₂, r, τ, j, v, g₀, hjinj, hjD, hτ, hDτ, hvu, hg₀div, -, hX⟩ :=
    exists_generator_factorization n π D hD M uu hMC Bn N ψ hψ hu hBn hBD x
  have : Nonempty (W₂ : V.Opens) := ⟨⟨x, hx₂⟩⟩
  have : Nonempty (cU' D M) := by
    have h := nonempty_inf_cU' D M (W := ⊤) ⟨⟨x, trivial⟩⟩
    obtain ⟨⟨y, -, hy⟩⟩ := h
    exact ⟨⟨y, hy⟩⟩
  have : Nonempty ((W₂ : V.Opens) ⊓ cU' D M : V.Opens) := nonempty_inf_cU' D M ‹_›
  have hW₃ : Nonempty (W ⊓ (W₂ : V.Opens) : V.Opens) := ⟨⟨x, hx, hx₂⟩⟩
  have : Nonempty ((W ⊓ (W₂ : V.Opens)) ⊓ cU' D M : V.Opens) := nonempty_inf_cU' D M hW₃
  set G := V.germToFunctionField ((W₂ : V.Opens) ⊓ cU' D M) g₀ with hGdef
  set b : Fin r → ℕ := fun k => (Bn (j k)).toNat with hb
  -- `G^N = ψ · v ∏ τₖ^{bₖ}` in the function field
  have hGN : G ^ N = ψK * V.germToFunctionField (W₂ : V.Opens) (v * ∏ k, τ k ^ b k) := by
    have h := congrArg (V.germToFunctionField ((W₂ : V.Opens) ⊓ cU' D M)) hX
    rw [map_pow, map_mul, germToFunctionField_map, germToFunctionField_map] at h
    rw [h, hψKdef, rationalFunctionsEquivFunctionField_eq_germ (U := cU' D M) (ψ : _) uu hu]
  -- the local equations do not vanish
  have hτ0 : ∀ k, τ k ≠ 0 := by
    intro k h0
    have hξ : genericPoint V ∈ (W₂ : V.Opens) :=
      ((genericPoint_spec V).mem_open_set_iff (W₂ : V.Opens).isOpen).2 ⟨x, trivial, hx₂⟩
    have h1 : genericPoint V ∈ (j k).support :=
      mem_support_of_ideal_eq_span (hτ k) hξ (by rw [h0, Scheme.basicOpen_zero]; exact id)
    exact MMP.Fourfold.genericPoint_notMem_supp D
      (MMP.Mori.DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp (hjD k)) h1)
  have hG0 : G ≠ 0 := by
    intro h0
    have hgerm : V.germToFunctionField (W₂ : V.Opens) (v * ∏ k, τ k ^ b k) ≠ 0 :=
      (map_ne_zero_iff _ (Scheme.germToFunctionField_injective V _)).2
        (mul_ne_zero hvu.ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hτ0 k)))
    have h1 := hGN
    rw [h0, zero_pow hN0] at h1
    exact mul_ne_zero hψK hgerm h1.symm
  -- the local section on `W ∩ W₂`
  have hle₃ : (W ⊓ (W₂ : V.Opens)) ⊓ cU' D M ≤ (W₂ : V.Opens) ⊓ cU' D M :=
    inf_le_inf_right _ inf_le_right
  have hG₃ : V.germToFunctionField ((W ⊓ (W₂ : V.Opens)) ⊓ cU' D M)
      (V.presheaf.map (homOfLE hle₃).op g₀) = G := germToFunctionField_map _ g₀
  refine Exists.imp (fun W' h => ⟨h.1, h.2.1.trans inf_le_left, h.2.2⟩)
    (exists_localRep_of_forall_primeDivisor n π D hD S M hSD p (W ⊓ (W₂ : V.Opens))
      (V.presheaf.map (homOfLE hle₃).op g₀)
      (DivCond.restrict (D := D) (M := M) inf_le_right hg₀div) (hG₃ ▸ hG0) ρ (fun E hE => ?_)
      ⟨hx, hx₂⟩)
  -- the three cases at a prime divisor `E`
  rw [hG₃]
  have hEW₂ : (E.support ∩ (W₂ : V.Opens)).Nonempty := hE.mono fun _ h => ⟨h.1, h.2.2⟩
  have hηW : E.genericPoint ∈ W := (E.genericPoint_mem_of_nonempty hE).1
  have hW₀ : ∀ y : V', g y = E.genericPoint → y ∈ g ⁻¹ᵁ W := fun y hy => by
    change g y ∈ W
    rw [hy]
    exact hηW
  have key : G⁻¹ • ρ = (c : V.functionField)⁻¹ • formsTrace ℂ V.functionField V'.functionField p
      ((z * (AlgebraicGeometry.functionFieldMap g G)⁻¹) • ω'₀) := by
    rw [hρ, smul_comm, ← map_smul, ← algebraMap_smul V'.functionField G⁻¹, smul_smul]
    congr 3
    change AlgebraicGeometry.functionFieldMap g G⁻¹ * z = _
    rw [map_inv₀, mul_comm]
  rw [key]
  have hb0 : ∀ k₀, j k₀ = E → E ∈ S.support → b k₀ = 0 := by
    intro k₀ hk₀ hES
    have h1 := hD.1 E (hSD E hES)
    have h2 := hSB E
    have h3 : 0 < S E := lt_of_le_of_ne (Finsupp.le_def.1 hS E)
      (Ne.symm (Finsupp.mem_support_iff.mp hES))
    simp only [hb, hk₀]
    split_ifs at h2 with h4
    · rw [h4]; rfl
    · omega
  let := MMP.Mori.stalkAlgebra π E.genericPoint
  have := MMP.Mori.isScalarTower_stalk_functionField π E.genericPoint
  refine ⟨fun hED => natCast_inv_smul_mem (k := ℂ) c ?_, fun hED => ?_, fun hES => ?_⟩
  · have h1 := formsTrace_mem_regLattice_of_factorization π g n hSD S' hS' hS'S W₂ τ j hjD hτ hvu
      b hN0 ψK G hψK hGN z hz p hθ' O'₀ hO'₀ E hEW₂ hW₀ hED
    convert h1 using 1
  · obtain ⟨y, hyE, hyW⟩ := hEW₂
    obtain ⟨k₀, hk₀⟩ := exists_eq_of_mem_chart (D := D) τ le_rfl j hτ hDτ hED hyW hyE
    by_cases hES : E ∈ S.support
    · refine natCast_inv_smul_mem (k := ℂ) c
        (Submodule.smul_le_right (I := maximalIdeal E.localRing) ?_)
      have h1 := formsTrace_mem_maximalIdeal_smul_logLattice_of_mem π g n S' hS' hS'S W₂ τ j hτ hvu
        b hN0 ψK G hψK hGN z hz p hθ' O'₀ hO'₀ E ⟨y, hyE, hyW⟩ hW₀ hk₀ hES
        (hb0 k₀ hk₀ hES) hjinj
      convert h1 using 1
    · have hbN : b k₀ < N := by
        have := hB E
        simp only [hb, hk₀]
        omega
      refine natCast_inv_smul_mem (k := ℂ) c ?_
      have h1 := formsTrace_mem_logLattice_of_factorization_of_notMem π g n S' hS' hS'S W₂ τ j hτ
        hvu b hN0 ψK G hψK hGN z hz p hθ' O'₀ hO'₀ E ⟨y, hyE, hyW⟩ hW₀ hk₀ hES hbN hjinj
      convert h1 using 1
  · obtain ⟨y, hyE, hyW⟩ := hEW₂
    obtain ⟨k₀, hk₀⟩ := exists_eq_of_mem_chart (D := D) τ le_rfl j hτ hDτ (hSD E hES) hyW hyE
    refine natCast_inv_smul_mem (k := ℂ) c ?_
    have h1 := formsTrace_mem_maximalIdeal_smul_logLattice_of_mem π g n S' hS' hS'S W₂ τ j hτ hvu
      b hN0 ψK G hψK hGN z hz p hθ' O'₀ hO'₀ E ⟨y, hyE, hyW⟩ hW₀ hk₀ hES
      (hb0 k₀ hk₀ hES) hjinj
    convert h1 using 1

end MMP.FourfoldProofs.FractionalLogComplexProof
