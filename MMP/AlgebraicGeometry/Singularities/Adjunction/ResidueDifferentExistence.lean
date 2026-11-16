module

public import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent

/-!
# Existence of the residue different

Let `Y` be a normal variety of dimension `n + 1` over a field `k` of characteristic zero and
`j : T ⟶ Y` the inclusion of a normal prime divisor `P`. Then `Y` carries a rational top form `τ`
with a simple pole along `P` and a nonzero Poincaré residue along `T`. Consequently, for a
`ℚ`-divisor `B_Y` with `coeff_P B_Y = 1` and `K_Y + B_Y` `ℚ`-Cartier, the residue different of
Kollár [SMMP, Def. 4.2] exists: `B_T = (div τ + B_Y)|_T - div(Res_T τ)` makes `(T, B_T)` an
adjunction step of `(Y, B_Y)` (`MMP.Fourfold.IsAdjunctionStep`).

## Main results

* `MMP.Fourfold.exists_ordForm_eq_neg_one_isPoincareResidue_of_charZero`: a form with a simple
  pole along `P` and a nonzero residue.
* `MMP.Fourfold.exists_topologicalKrullDim_eq_add_one`: a variety with a prime divisor has
  positive dimension.
* `MMP.Fourfold.exists_isAdjunctionStep_of_isQCartier`: the residue different exists when
  `K_Y + B_Y` is `ℚ`-Cartier.

## References

* [J. Kollár, *Singularities of the minimal model program*][Kollar2013], Definition 4.2
-/

public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- The top exterior power of a linearly independent family is nonzero. -/
private theorem ιMulti_ne_zero_of_linearIndependent {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] {n : ℕ} {v : Fin n → W} (hv : LinearIndependent K v) :
    exteriorPower.ιMulti K n v ≠ 0 := by
  classical
  let b := Module.Basis.span hv
  have hmap : exteriorPower.map n (Submodule.span K (Set.range v)).subtype
      (exteriorPower.ιMulti K n b) = exteriorPower.ιMulti K n v := by
    rw [exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    simp [b, Module.Basis.span_apply]
  intro h0
  have h1 : exteriorPower.ιMulti K n b = 0 := by
    apply exteriorPower.map_injective_field (n := n) (Submodule.injective_subtype _)
    rw [hmap, h0, map_zero]
  have h2 := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) h1
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero, b.det_self] at h2
  exact one_ne_zero h2

/-- A nonzero element of the maximal ideal of the local ring at the generic point of a prime
divisor. -/
private theorem exists_mem_maximalIdeal_ne_zero {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (P : MMP.Mori.PrimeDivisor X) (y : X)
    (hy : y = P.genericPoint) :
    ∃ t : X.presheaf.stalk y, t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) ∧
      algebraMap (X.presheaf.stalk y) X.functionField t ≠ 0 := by
  subst hy
  have := P.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
  exact ⟨ϖ, hϖ.not_isUnit, (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero⟩

/-- In characteristic zero, a field essentially of finite type over `k` of transcendence degree
`n` has `n` elements with linearly independent differentials. -/
theorem exists_linearIndependent_D_of_toNat_trdeg {k L : Type*} [Field k] [CharZero k] [Field L]
    [Algebra k L] [Algebra.EssFiniteType k L] {n : ℕ} (h : (Algebra.trdeg k L).toNat = n) :
    ∃ y : Fin n → L, LinearIndependent L fun i => KaehlerDifferential.D k L (y i) := by
  have hfin : Module.finrank L Ω[L⁄k] = n := (finrank_kaehlerDifferential_eq_trdeg k L).trans h
  have : FiniteDimensional L Ω[L⁄k] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k L).1
  obtain ⟨b, hbsub, hbspan, hbli⟩ :=
    exists_linearIndependent L (Set.range (KaehlerDifferential.D k L))
  have hbtop : Submodule.span L (Set.range ((↑) : b → Ω[L⁄k])) = ⊤ := by
    rw [Subtype.range_coe, hbspan, KaehlerDifferential.span_range_derivation]
  let bb := Module.Basis.mk hbli hbtop.ge
  have : Finite b := Module.Finite.finite_basis bb
  letI : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = n := by rw [← Module.finrank_eq_card_basis bb, hfin]
  let e : Fin n ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  choose y hy using fun i : Fin n => hbsub (e i).2
  refine ⟨y, ?_⟩
  convert hbli.comp e e.injective using 1
  funext i
  simp only [Function.comp_apply, hy]

/-- **A form with a simple pole along a normal prime divisor and a nonzero residue.** Let `M` be
a normal variety of dimension `n + 1` over a field `k` of characteristic zero and `j : S ⟶ M` the
inclusion of a normal prime divisor `P`. There is a rational top form `τ ≠ 0` on `M` with
`ord_P τ = -1` and a nonzero Poincaré residue `ρ = Res_S τ`. -/
theorem exists_ordForm_eq_neg_one_isPoincareResidue_of_charZero {k : Type} [Field k] [CharZero k]
    {M S : Scheme.{0}} (sM : M ⟶ Spec (.of k))
    [IsIntegral M] [IsNormal M] [IsLocallyNoetherian M] [LocallyOfFiniteType sM] {n : ℕ}
    (hdim : topologicalKrullDim M = n + 1) (j : S ⟶ M) [IsClosedImmersion j] [IsIntegral S]
    (P : MMP.Mori.PrimeDivisor M) (hP : Set.range j.base = (P.support : Set M)) :
    ∃ τ : RationalPluriForms sM (n + 1) 1, τ ≠ 0 ∧ P.ordForm τ = -1 ∧
      ∃ ρ : RationalPluriForms (j ≫ sM) n 1, IsPoincareResidue sM j n 1 τ ρ ∧ ρ ≠ 0 := by
  classical
  have hjT := MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hP
  letI := functionFieldAlgebra sM
  letI := functionFieldAlgebra (j ≫ sM)
  have hd : (Algebra.trdeg k M.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sM) (by rw [hdim]; norm_cast)
  have hdimT := MMP.Fourfold.topologicalKrullDim_eq_of_range_eq_support sM hdim j P hP
  -- coordinates on `S` with independent differentials
  have := essFiniteType_functionField (sX := j ≫ sM)
  obtain ⟨xb, hxb⟩ := exists_linearIndependent_D_of_toNat_trdeg (k := k)
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq hdimT)
  choose x hx using fun i => SurjectiveOnStalks.stalkMap_surjective j (genericPoint S) (xb i)
  obtain ⟨t, htm, ht0⟩ := exists_mem_maximalIdeal_ne_zero P (j (genericPoint S)) hjT
  letI := stalkAlgebra sM (j (genericPoint S))
  let ν : MvPolynomial (Fin (n + 1)) k →ₐ[k] M.presheaf.stalk (j (genericPoint S)) :=
    MvPolynomial.aeval (Fin.cons t x)
  have hν0 : ν (MvPolynomial.X 0) = t := by simp [ν]
  have hνs : ∀ i : Fin n, ν (MvPolynomial.X i.succ) = x i := fun i => by simp [ν]
  have hli : LinearIndependent S.functionField fun i : Fin n => KaehlerDifferential.D k
      S.functionField ((j.stalkMap (genericPoint S)).hom (ν (MvPolynomial.X i.succ))) := by
    simpa only [hνs, hx] using hxb
  have hF : (algebraMap _ M.functionField t)⁻¹ *
      algebraMap _ M.functionField (ν (MvPolynomial.X 0)) =
      algebraMap _ M.functionField (1 : M.presheaf.stalk (j (genericPoint S))) := by
    rw [hν0, inv_mul_cancel₀ ht0, map_one]
  obtain ⟨c, hc, hres, hord⟩ := exists_isPoincareResidue_smul_tprod_ιMulti sM hd j P hjT ν
    (by rw [hν0]; exact htm) (fun h => ht0 (by rw [← hν0, h, map_zero]))
    hli hF
  refine ⟨_, fun h0 => ?_, hord isUnit_one, _, hres, ?_⟩
  · simpa [h0] using hord isUnit_one
  · rw [map_one, mul_one]
    haveI : CharZero S.functionField :=
      charZero_of_injective_algebraMap (algebraMap k S.functionField).injective
    refine smul_ne_zero (Nat.cast_ne_zero.mpr hc.ne') fun h0 => ?_
    have h1 := congrArg (PiTensorProduct.subsingletonEquiv (R := S.functionField)
      (s := fun _ : Fin 1 => ⋀[S.functionField]^n Ω[S.functionField⁄k]) 0) h0
    rw [PiTensorProduct.subsingletonEquiv_apply_tprod] at h1
    exact ιMulti_ne_zero_of_linearIndependent hli (h1.trans (LinearEquiv.map_zero _))

/-- A scheme carrying a prime divisor, locally of finite type over a field, has dimension at least
one: a prime divisor of an `N`-dimensional variety has dimension `N - 1`. -/
private theorem exists_eq_add_one_of_primeDivisor {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {N : ℕ}
    (hN : topologicalKrullDim X = N) (P : MMP.Mori.PrimeDivisor X) : ∃ n, N = n + 1 := by
  have hPP := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX P.genericPoint
  rw [P.coheight_genericPoint, hN] at hPP
  rcases N with _ | n
  · exfalso
    revert hPP
    generalize topologicalKrullDim (closure {P.genericPoint} : Set X) = e
    induction e using WithBot.recBotCoe with
    | bot => simp
    | coe m =>
      induction m using ENat.recTopCoe with
      | top => norm_cast
      | coe m => norm_cast
  · exact ⟨n, rfl⟩

/-- An integral scheme locally of finite type over a field which carries a prime divisor has
dimension `n + 1` for some `n`. -/
theorem exists_topologicalKrullDim_eq_add_one {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (P : MMP.Mori.PrimeDivisor X) : ∃ n : ℕ, topologicalKrullDim X = n + 1 := by
  have h := topologicalKrullDim_eq_toNat_trdeg sX
  obtain ⟨n, hn⟩ := exists_eq_add_one_of_primeDivisor sX h P
  refine ⟨n, ?_⟩
  rw [h, hn]
  push_cast
  rfl

/-- **The residue different exists** (Kollár [SMMP, Def. 4.2]). Let `Y` be a normal variety of
dimension `n + 1` over a field of characteristic zero with a canonical divisor `K`, `B_Y` a
`ℚ`-divisor with `K + B_Y` `ℚ`-Cartier, and `j : T ⟶ Y` a closed immersion of a normal variety
onto a prime divisor `P` with `coeff_P B_Y = 1`. Then there is an adjunction step
`(Y, B_Y) ⇝ (T, B_T)`: for a form `τ` with a simple pole along `P` and residue `ρ`, `div τ ∼ K`,
so `div τ + B_Y` is `ℚ`-Cartier, its support does not contain `T`, and
`B_T = (div τ + B_Y)|_T - div ρ`. -/
theorem exists_isAdjunctionStep_of_isQCartier {k : Type} [Field k] [CharZero k]
    {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : IsNormalVariety k sY) {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY (n + 1))
    {BY : QDivisor Y} (hQ : (Divisor.toQDivisor K + BY).IsQCartier) (P : MMP.Mori.PrimeDivisor Y)
    (hP : BY.coeff P = 1) (j : T ⟶ Y) [IsClosedImmersion j]
    (hj : Set.range j.base = (P.support : Set Y)) (hT : IsNormalVariety k (j ≫ sY)) :
    ∃ BT : QDivisor T, IsAdjunctionStep sY BY j BT := by
  classical
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : CompactSpace Y := haveI := hY.1; QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsIntegral T := hT.1.toIsIntegral
  haveI : IsNormal T := hT.2
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (j ≫ sY)
  haveI : CompactSpace T := haveI := hT.1; QuasiCompact.compactSpace_of_compactSpace (j ≫ sY)
  have hdim : topologicalKrullDim Y = n + 1 := by
    rw [hK.topologicalKrullDim_eq]
    push_cast
    rfl
  obtain ⟨τ, hτ0, hτP, ρ, hρ, -⟩ :=
    exists_ordForm_eq_neg_one_isPoincareResidue_of_charZero sY hdim j P hj
  have hlin := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK hτ0
  rw [one_smul] at hlin
  have hD : (Divisor.toQDivisor (divisorOfForm τ) + BY).IsQCartier :=
    hQ.add_of_linearlyEquivalent hlin.symm
  have hgen : ∀ Z : irreducibleComponents T,
      j (componentGenericPoint T Z) ∉ (Divisor.toQDivisor (divisorOfForm τ) + BY).supp := by
    intro Z hZ
    rw [componentGenericPoint_eq_genericPoint,
      MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hj] at hZ
    obtain ⟨E, hE, hPE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    obtain rfl := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hPE
    apply hE
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hτP, hP]
    norm_num
  refine ⟨(Divisor.toQDivisor (divisorOfForm τ) + BY).pullback hD hgen -
      Divisor.toQDivisor (divisorOfForm ρ), hT, P, hP.ge, hj, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, n, hY, hdim, τ, hτ0, hτP, hD, ρ, hρ, hgen, ?_⟩
  rw [add_sub_cancel]
  exact QDivisor.isPullback_pullback hD hgen

end MMP.Fourfold

end
