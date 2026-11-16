module

public import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
public import MMP.AlgebraicGeometry.MMP.BasepointFree.UniformRelativeFreeness

/-!
# Fixed-part uniformity from one big-boundary model

Let `φ : X ⤏ Y` be a birational contraction over a projective variety `Z` of normal
`ℚ`-factorial projective complex varieties, with a common projective birational model
`p : T ⟶ X`, `q : T ⟶ Y`. Let `D_t` (`t` in a rational affine subspace `V ⊆ ℝ^s`) be a rational
affine family of `ℝ`-Cartier divisors on `X` with fixed finite support, whose push-forwards are
`φ_* D_t = K_Y + Γ_t` for a rational affine family `Γ_t`, and such that `E_t = p^*D_t - q^*φ_*D_t`
is `q`-exceptional. If at `δ ∈ V` the boundary `Γ_δ` is effective klt and contains an effective
`ℚ`-divisor big over `Z`, `E_δ ≥ 0` and `K_Y + Γ_δ` is nef over `Z`, then the relative
divisorial stable base primes of `D_δ` persist near `δ` in `V`, and, near `δ` in the smallest
rational affine subspace `W` containing `δ`, every fixed component of a sufficiently divisible
integral multiple of `D_t` is a stable base prime of `D_δ`.

The proof writes `K_Y + Γ_δ` as a combination of relatively free Cartier divisors with the
uniform freeness theorem on `Y`, reads off the stable base primes of `D_δ` from `p_* E_δ`, and
compares fixed parts on the common model. The families are encoded by rational affine
coefficient forms on finitely many primes; on `Y` and `T` these are obtained from
`ℚ`-factoriality.

## Main results

* `MMP.Fourfold.isInRelativeDivisorialStableBase_uniformity_of_isBirationalContraction`.

## Implementation notes

The parameter space is `ℝ^s` (`Fin s → ℝ`); a rational affine family is given by finitely many
prime divisors `Pᵢ` carrying the support and rational affine coefficient functions
`MMP.Fourfold.ratAffineForm`. The pull-backs `p^*D_t`, `q^*D'_t` are the divisors determined by
`MMP.Flips.IsRCartierPullback`, and `q`-exceptionality of `E_t` is `q_* E_t = 0`. The smallest
rational affine hull is `MMP.Fourfold.rationalAffineHull δ`. "`k D_t / r` integral Cartier" is
`k D_t = r C` for an integral Cartier divisor `C`; the relative fixed part of the integral divisor
`r C` is read off `MMP.Fourfold.relativeFixedMultiplicity`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Filter Topology

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

-- Rational maps through function fields

section RationalMaps

variable {X Y Z T : Scheme.{0}}

private theorem genericPoint_mem_of_nonempty [IrreducibleSpace X] {U : X.Opens}
    (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  (genericPoint_specializes _).mem_open U.2 hU.choose_spec

private theorem isDominant_fromSpecStalk_genericPoint (X : Scheme.{0}) [IrreducibleSpace X] :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  refine ⟨Dense.mono (Set.singleton_subset_iff.mpr ⟨_, Scheme.fromSpecStalk_closedPoint⟩) ?_⟩
  rw [dense_iff_closure_eq, (genericPoint_spec X).def]

/-- If `ψ'` is an inverse of `ψ : X ⤏ Y` and `φ : Spec k(X) ⟶ Spec k(Y)` lifts
`Spec k(X) ⟶ Y` along `ψ`, then `Spec k(X) ⟶ Spec k(Y) ⟶ X` along `ψ'` is the canonical map. -/
private theorem comp_fromFunctionField_eq_of_isInverse [IsIntegral X] [IsIntegral Y]
    {ψ : X.RationalMap Y} {ψ' : Y.RationalMap X} (hinv : MMP.Mori.RationalMap.IsInverse ψ ψ')
    (φ : Spec X.functionField ⟶ Spec Y.functionField)
    (hφ : φ ≫ Y.fromSpecStalk (genericPoint Y) = ψ.fromFunctionField) :
    φ ≫ ψ'.fromFunctionField = X.fromSpecStalk (genericPoint X) := by
  obtain ⟨e, he1, he2⟩ := hinv
  have hx : genericPoint X ∈ e.source := genericPoint_mem_of_nonempty e.dense_source.nonempty
  have hy : genericPoint Y ∈ e.target := genericPoint_mem_of_nonempty e.dense_target.nonempty
  have hψ : ψ.fromFunctionField = e.source.fromSpecStalkOfMem (genericPoint X) hx ≫
      e.iso.hom ≫ e.target.ι := by
    rw [← he1, Scheme.RationalMap.fromFunctionField_toRationalMap]
    rfl
  have hψ' : ψ'.fromFunctionField = e.target.fromSpecStalkOfMem (genericPoint Y) hy ≫
      e.iso.inv ≫ e.source.ι := by
    rw [← he2, Scheme.RationalMap.fromFunctionField_toRationalMap]
    rfl
  have c : φ ≫ e.target.fromSpecStalkOfMem (genericPoint Y) hy =
      e.source.fromSpecStalkOfMem (genericPoint X) hx ≫ e.iso.hom := by
    rw [← cancel_mono e.target.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hφ, hψ,
      Category.assoc]
  rw [hψ', ← Category.assoc, c, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- On a common model `p : T ⟶ X`, `q : T ⟶ Y` of a rational map `φ` over `Z`, with `Z`
separated, the two composites `T ⟶ Z` agree. -/
private theorem comp_eq_comp_of_isOver_of_comp_eq {S : Scheme.{0}} (sZ : Z ⟶ S) [IsSeparated sZ]
    [IsIntegral T] [IsIntegral X] (fX : X ⟶ Z) (fY : Y ⟶ Z) {φ : X.RationalMap Y}
    (hover : MMP.Flips.RationalMap.IsOver fX fY φ) (p : T ⟶ X) (q : T ⟶ Y) [IsDominant p]
    {h : X.RationalMap T} (hh : MMP.Mori.RationalMap.IsInverse p.toRationalMap h)
    (hhq : h.compHom q = φ) (hs : (p ≫ fX) ≫ sZ = (q ≫ fY) ≫ sZ) : p ≫ fX = q ≫ fY := by
  have := isDominant_fromSpecStalk_genericPoint T
  refine ext_of_isDominant_of_isSeparated sZ hs (T.fromSpecStalk (genericPoint T)) ?_
  set σ : Spec T.functionField ⟶ Spec X.functionField :=
    Spec.map (CommRingCat.ofHom (functionFieldMap p))
  have hσ : σ ≫ X.fromSpecStalk (genericPoint X) = T.fromSpecStalk (genericPoint T) ≫ p :=
    functionFieldMap_fromSpecStalk p
  have h1 : σ ≫ h.fromFunctionField = T.fromSpecStalk (genericPoint T) :=
    comp_fromFunctionField_eq_of_isInverse hh σ
      (by rw [hσ, MMP.Flips.RationalMap.fromFunctionField_hom])
  have h2 : φ.fromFunctionField ≫ fY = X.fromSpecStalk (genericPoint X) ≫ fX := by
    rw [← MMP.Flips.RationalMap.fromFunctionField_compHom, hover,
      MMP.Flips.RationalMap.fromFunctionField_hom]
  calc T.fromSpecStalk (genericPoint T) ≫ p ≫ fX
      = σ ≫ X.fromSpecStalk (genericPoint X) ≫ fX := by rw [reassoc_of% hσ]
    _ = σ ≫ φ.fromFunctionField ≫ fY := by rw [h2]
    _ = σ ≫ h.fromFunctionField ≫ q ≫ fY := by
      rw [← hhq, MMP.Flips.RationalMap.fromFunctionField_compHom, Category.assoc]
    _ = T.fromSpecStalk (genericPoint T) ≫ q ≫ fY := by rw [reassoc_of% h1]

end RationalMaps

-- Rational affine families of divisors

section Families

variable {s : ℕ}

private theorem ratAffineForm_zero (t : Fin s → ℝ) : ratAffineForm (0 : (Fin s → ℚ) × ℚ) t = 0 := by
  simp [ratAffineForm]

private theorem ratAffineForm_add (f g : (Fin s → ℚ) × ℚ) (t : Fin s → ℝ) :
    ratAffineForm (f + g) t = ratAffineForm f t + ratAffineForm g t := by
  simp only [ratAffineForm, Prod.fst_add, Prod.snd_add, Pi.add_apply, Rat.cast_add, add_mul,
    Finset.sum_add_distrib]
  ring

private theorem ratAffineForm_smul (c : ℚ) (f : (Fin s → ℚ) × ℚ) (t : Fin s → ℝ) :
    ratAffineForm (c • f) t = c * ratAffineForm f t := by
  simp only [ratAffineForm, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
    Rat.cast_mul, mul_add, Finset.mul_sum, mul_assoc]

private theorem ratAffineForm_sub (f g : (Fin s → ℚ) × ℚ) (t : Fin s → ℝ) :
    ratAffineForm (f - g) t = ratAffineForm f t - ratAffineForm g t := by
  simp only [ratAffineForm, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, Rat.cast_sub, sub_mul,
    Finset.sum_sub_distrib]
  ring

private theorem ratAffineForm_const (q : ℚ) (t : Fin s → ℝ) :
    ratAffineForm ((0, q) : (Fin s → ℚ) × ℚ) t = q := by
  simp [ratAffineForm]

private theorem coeff_finset_sum {X : Scheme.{0}} {ι : Type*} (I : Finset ι)
    (f : ι → RDivisor X) (E : Mori.PrimeDivisor X) :
    (∑ i ∈ I, f i).coeff E = ∑ i ∈ I, (f i).coeff E :=
  map_sum (DivisorWithCoeffs.coeffAddMonoidHom E) f I

private theorem ratAffineForm_sum {ι : Type*} (I : Finset ι) (f : ι → (Fin s → ℚ) × ℚ)
    (t : Fin s → ℝ) : ratAffineForm (∑ i ∈ I, f i) t = ∑ i ∈ I, ratAffineForm (f i) t := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [ratAffineForm_zero]
  | insert i I hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ratAffineForm_add, ih]

/-- A family of real divisors whose coefficients are rational affine functions of the
parameter, all supported in one finite set of primes. -/
private def IsRatAffineFamily {X : Scheme.{0}} (F : (Fin s → ℝ) → RDivisor X) : Prop :=
  ∃ (S : Finset (Mori.PrimeDivisor X)) (β : Mori.PrimeDivisor X → (Fin s → ℚ) × ℚ),
    (∀ P ∉ S, β P = 0) ∧ ∀ t P, (F t).coeff P = ratAffineForm (β P) t

variable {X : Scheme.{0}}

private theorem isRatAffineFamily_of_coeff (F : (Fin s → ℝ) → RDivisor X) {n : ℕ}
    (PX : Fin n → Mori.PrimeDivisor X) (a : Fin n → (Fin s → ℚ) × ℚ)
    (hcoeff : ∀ t i, (F t).coeff (PX i) = ratAffineForm (a i) t)
    (hsupp : ∀ t, ↑(F t).support ⊆ Set.range PX) : IsRatAffineFamily F := by
  classical
  refine ⟨Finset.univ.image PX, fun P => if h : P ∈ Set.range PX then a h.choose else 0, ?_, ?_⟩
  · intro P hP
    have : P ∉ Set.range PX := fun ⟨i, hi⟩ => hP (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)
    simp [this]
  · intro t P
    dsimp only
    by_cases h : P ∈ Set.range PX
    · rw [dif_pos h, ← hcoeff t h.choose, h.choose_spec]
    · rw [dif_neg h, ratAffineForm_zero]
      by_contra h0
      exact h (hsupp t (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 h0)))

private theorem IsRatAffineFamily.const_add {F : (Fin s → ℝ) → RDivisor X}
    (hF : IsRatAffineFamily F) (K : Divisor X) :
    IsRatAffineFamily (fun t => Divisor.toRDivisor K + F t) := by
  classical
  obtain ⟨S, β, hS, hβ⟩ := hF
  refine ⟨S ∪ K.support, fun P => β P + (0, (K.coeff P : ℚ)), fun P hP => ?_, fun t P => ?_⟩
  · rw [Finset.mem_union, not_or] at hP
    have hK : K.coeff P = 0 := Finsupp.notMem_support_iff.1 hP.2
    dsimp only
    rw [hS P hP.1, hK]
    simp
  · rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, hβ, ratAffineForm_add,
      ratAffineForm_const]
    push_cast
    ring

private theorem IsRatAffineFamily.sub {F G : (Fin s → ℝ) → RDivisor X}
    (hF : IsRatAffineFamily F) (hG : IsRatAffineFamily G) :
    IsRatAffineFamily (fun t => F t - G t) := by
  classical
  obtain ⟨S, β, hS, hβ⟩ := hF
  obtain ⟨S', γ, hS', hγ⟩ := hG
  refine ⟨S ∪ S', fun P => β P - γ P, fun P hP => ?_, fun t P => ?_⟩
  · rw [Finset.mem_union, not_or] at hP
    dsimp only
    rw [hS P hP.1, hS' P hP.2, sub_zero]
  · rw [DivisorWithCoeffs.coeff_sub, hβ, hγ, ratAffineForm_sub]

private theorem IsRatAffineFamily.exists_finset {F : (Fin s → ℝ) → RDivisor X}
    (hF : IsRatAffineFamily F) : ∃ S : Finset (Mori.PrimeDivisor X), ∀ t, (F t).support ⊆ S := by
  obtain ⟨S, β, hS, hβ⟩ := hF
  refine ⟨S, fun t P hP => ?_⟩
  by_contra h
  apply Finsupp.mem_support_iff.1 hP
  have := hβ t P
  rw [hS P h, ratAffineForm_zero] at this
  exact this

private theorem IsRatAffineFamily.exists_affineMap {F : (Fin s → ℝ) → RDivisor X}
    (hF : IsRatAffineFamily F) : ∃ L : (Fin s → ℝ) →ᵃ[ℝ] RDivisor X, ∀ t, L t = F t := by
  classical
  obtain ⟨S, β, hS, hβ⟩ := hF
  let ℓ : Mori.PrimeDivisor X → (Fin s → ℝ) →ₗ[ℝ] ℝ := fun P =>
    ∑ j, ((β P).1 j : ℝ) • LinearMap.proj j
  have hℓ : ∀ P v, ℓ P v = ∑ j, ((β P).1 j : ℝ) * v j := fun P v => by simp [ℓ]
  let lin : (Fin s → ℝ) →ₗ[ℝ] RDivisor X :=
    ∑ P ∈ S, LinearMap.smulRight (ℓ P) (Finsupp.single P (1 : ℝ))
  have hlin : ∀ v P, (lin v).coeff P = ℓ P v := fun v P => by
    simp only [lin, LinearMap.sum_apply, LinearMap.smulRight_apply, coeff_finset_sum,
      DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_apply, Finsupp.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']
    rw [Finsupp.finset_sum_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq']
    split_ifs with hP
    · rfl
    · rw [hℓ, hS P hP]; simp
  refine ⟨⟨F, lin, fun t v => ?_⟩, fun t => rfl⟩
  ext P
  change (F (v + t)).coeff P = (lin v + F t).coeff P
  rw [DivisorWithCoeffs.coeff_add, hlin, hℓ, hβ, hβ]
  simp only [ratAffineForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

/-- A rational affine relation among the coefficients of `F δ` holds for `F t` along the
smallest rational affine hull of `δ`. -/
private theorem IsRatAffineFamily.relation {F : (Fin s → ℝ) → RDivisor X}
    (hF : IsRatAffineFamily F) {δ t : Fin s → ℝ} (ht : t ∈ rationalAffineHull δ)
    (c : Mori.PrimeDivisor X →₀ ℚ) (q : ℚ)
    (hc : (c.sum fun P cP => (cP : ℝ) * (F δ).coeff P) = q) :
    (c.sum fun P cP => (cP : ℝ) * (F t).coeff P) = q := by
  obtain ⟨S, β, hS, hβ⟩ := hF
  have key : ∀ u, (c.sum fun P cP => (cP : ℝ) * (F u).coeff P) =
      ratAffineForm (∑ P ∈ c.support, c P • β P) u := fun u => by
    rw [Finsupp.sum, ratAffineForm_sum]
    exact Finset.sum_congr rfl fun P _ => by rw [ratAffineForm_smul, hβ]
  rw [key] at hc ⊢
  have := mem_rationalAffineHull.1 ht (∑ P ∈ c.support, c P • β P - (0, q))
    (by rw [ratAffineForm_sub, hc, ratAffineForm_const, sub_self])
  rw [ratAffineForm_sub, ratAffineForm_const] at this
  linarith

private theorem IsRatAffineFamily.eventually_nonneg {F : (Fin s → ℝ) → RDivisor X}
    (hF : IsRatAffineFamily F) {V : Set (Fin s → ℝ)} (hV : IsRationalAffineSubspace V)
    {δ : Fin s → ℝ} (hδV : δ ∈ V) (hδ : 0 ≤ F δ) :
    (rationalAffineHull δ : Set (Fin s → ℝ)) ⊆ V ∧
      ∀ᶠ t in 𝓝[(rationalAffineHull δ : Set (Fin s → ℝ))] δ,
        0 ≤ F t ∧ (F t).support = (F δ).support := by
  obtain ⟨S, β, hS, hβ⟩ := hF
  refine exceptional_support_rational_hull (fun i => (S.equivFin.symm i : Mori.PrimeDivisor X))
    (fun i => β (S.equivFin.symm i)) F (fun t i => hβ t _) (fun t P hP => ?_) hV hδV hδ
  have hPS : P ∈ S := by
    by_contra h
    apply Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hP)
    have := hβ t P
    rw [hS P h, ratAffineForm_zero] at this
    exact this
  exact ⟨S.equivFin ⟨P, hPS⟩, by simp⟩

/-- On a scheme on which every Weil divisor has a Cartier multiple, the pull-back of a rational
affine family along a dominant morphism is again a rational affine family. -/
private theorem IsRatAffineFamily.exists_isRCartierPullback [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X] {T : Scheme.{0}} [IsLocallyNoetherian T] [IsNormal T] [IsIntegral T]
    [CompactSpace T] {F : (Fin s → ℝ) → RDivisor X} (hF : IsRatAffineFamily F)
    (hQ : ∀ D : Divisor X, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier) (f : T ⟶ X)
    [IsDominant f] :
    ∃ G : (Fin s → ℝ) → RDivisor T, IsRatAffineFamily G ∧
      ∀ t, MMP.Flips.IsRCartierPullback f (F t) (G t) := by
  classical
  obtain ⟨S, β, hS, hβ⟩ := hF
  choose m hm hmC using fun P : Mori.PrimeDivisor X => hQ (Finsupp.single P 1)
  set L : Mori.PrimeDivisor X → Divisor X := fun P => (m P : ℤ) • Finsupp.single P 1 with hLdef
  set L' : Mori.PrimeDivisor X → Divisor T := fun P => (L P).pullback (hmC P)
    (map_componentGenericPoint_notMem_supp_of_isDominant f (L P)) with hL'def
  refine ⟨fun t => ∑ P ∈ S, (ratAffineForm (β P) t / m P) • Divisor.toRDivisor (L' P),
    ⟨S.biUnion fun P => (L' P).support,
      fun E => ∑ P ∈ S, (((L' P).coeff E : ℚ) / m P) • β P, fun E hE => ?_, fun t E => ?_⟩,
    fun t => ?_⟩
  · refine Finset.sum_eq_zero fun P hP => ?_
    have : (L' P).coeff E = 0 := by
      by_contra h
      exact hE (Finset.mem_biUnion.2 ⟨P, hP, Finsupp.mem_support_iff.2 h⟩)
    rw [this]
    simp
  · rw [ratAffineForm_sum, coeff_finset_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [ratAffineForm_smul, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    push_cast
    ring
  · have hFt : F t = ∑ P ∈ S, (ratAffineForm (β P) t / m P) • Divisor.toRDivisor (L P) := by
      ext E
      change (F t).coeff E = (∑ P ∈ S, (ratAffineForm (β P) t / m P) •
        Divisor.toRDivisor (L P)).coeff E
      rw [coeff_finset_sum, hβ]
      have hterm : ∀ P ∈ S, ((ratAffineForm (β P) t / m P) • Divisor.toRDivisor (L P)).coeff E =
          if P = E then ratAffineForm (β P) t else 0 := fun P _ => by
        rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, hLdef]
        dsimp only
        rw [DivisorWithCoeffs.coeff_smul]
        by_cases hPE : P = E
        · subst hPE
          have : (m P : ℝ) ≠ 0 := by exact_mod_cast (hm P).ne'
          rw [if_pos rfl, DivisorWithCoeffs.coeff_single_self, smul_eq_mul, smul_eq_mul, mul_one,
            Int.cast_natCast]
          field_simp
        · rw [if_neg hPE, DivisorWithCoeffs.coeff_single_of_ne hPE]
          simp
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
      split_ifs with hE
      · rfl
      · rw [hS E hE, ratAffineForm_zero]
    rw [hFt]
    exact isRCartierPullback_sum S _ _ fun P _ => isRCartierPullback_smul _
      (isRCartierPullback_toRDivisor (hmC P) _ (Divisor.isPullback_pullback (hmC P) _))

end Families

-- Convex geometry

section Convex

/-- If `Δ` lies in the algebraic relative interior of a convex set `C`, then from `Δ` one can
move a little towards every point of the affine span of `C` without leaving `C`. -/
private theorem exists_lineMap_mem_of_mem_affineSpan {M : Type*} [AddCommGroup M] [Module ℝ M]
    {C : Set M} (hC : Convex ℝ C) {Δ : M} (hΔ : Δ ∈ C)
    (hrel : ∀ x ∈ C, ∃ ε : ℝ, 0 < ε ∧ Δ + ε • (Δ - x) ∈ C) {y : M}
    (hy : y ∈ affineSpan ℝ C) : ∃ ε : ℝ, 0 < ε ∧ AffineMap.lineMap Δ y ε ∈ C := by
  -- the directions along which one can leave `Δ` inside `C`
  let K : Set M := {u | ∃ ε : ℝ, 0 < ε ∧ Δ + ε • u ∈ C}
  have shrink : ∀ {u : M} {ε : ℝ}, 0 < ε → Δ + ε • u ∈ C → ∀ ε', 0 ≤ ε' → ε' ≤ ε →
      Δ + ε' • u ∈ C := fun {u ε} hε hu ε' h0 h1 => by
    have := hC.add_smul_sub_mem hΔ hu ⟨div_nonneg h0 hε.le, (div_le_one hε).2 h1⟩
    rwa [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hε.ne'] at this
  have hadd : ∀ u v, u ∈ K → v ∈ K → u + v ∈ K := by
    rintro u v ⟨ε₁, hε₁, hu⟩ ⟨ε₂, hε₂, hv⟩
    set ε := min ε₁ ε₂
    have hε : 0 < ε := lt_min hε₁ hε₂
    have hu' := shrink hε₁ hu ε hε.le (min_le_left _ _)
    have hv' := shrink hε₂ hv ε hε.le (min_le_right _ _)
    refine ⟨ε / 2, half_pos hε, ?_⟩
    have := hC hu' hv' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    convert this using 1
    module
  have hsmul : ∀ (c : ℝ) u, 0 < c → u ∈ K → c • u ∈ K := by
    rintro c u hc ⟨ε, hε, hu⟩
    exact ⟨ε / c, div_pos hε hc, by rwa [smul_smul, div_mul_cancel₀ _ hc.ne']⟩
  have hzero : (0 : M) ∈ K := ⟨1, one_pos, by simpa using hΔ⟩
  -- every vector of the span, and its negative, is such a direction
  have hdir : y -ᵥ Δ ∈ vectorSpan ℝ C := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction hy (subset_affineSpan ℝ C hΔ)
  rw [vectorSpan_eq_span_vsub_set_right ℝ hΔ] at hdir
  have key : ∀ u ∈ Submodule.span ℝ ((· -ᵥ Δ) '' C), u ∈ K ∧ -u ∈ K := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      refine ⟨⟨1, one_pos, by simpa using hx⟩, ?_⟩
      obtain ⟨ε, hε, h⟩ := hrel x hx
      exact ⟨ε, hε, by simpa [vsub_eq_sub, neg_sub] using h⟩
    | zero => exact ⟨hzero, by simpa using hzero⟩
    | add u v _ _ hu hv => exact ⟨hadd u v hu.1 hv.1, by rw [neg_add]; exact hadd _ _ hu.2 hv.2⟩
    | smul c u _ hu =>
      rcases lt_trichotomy c 0 with hc | rfl | hc
      · refine ⟨?_, ?_⟩
        · rw [show c • u = (-c) • -u by simp]; exact hsmul _ _ (neg_pos.2 hc) hu.2
        · rw [show -(c • u) = (-c) • u by simp]; exact hsmul _ _ (neg_pos.2 hc) hu.1
      · rw [zero_smul, neg_zero]; exact ⟨hzero, hzero⟩
      · exact ⟨hsmul c u hc hu.1, by rw [← smul_neg]; exact hsmul c _ hc hu.2⟩
  obtain ⟨ε, hε, h⟩ := (key _ hdir).1
  refine ⟨ε, hε, ?_⟩
  rw [AffineMap.lineMap_apply_module', add_comm]
  simpa [vsub_eq_sub] using h

/-- A convex set containing `δ` which absorbs every direction of the smallest rational affine
hull `W` of `δ` is a neighbourhood of `δ` in `W`. -/
private theorem mem_nhdsWithin_rationalAffineHull_of_convex {s : ℕ} {U : Set (Fin s → ℝ)}
    (hU : Convex ℝ U) {δ : Fin s → ℝ} (hδ : δ ∈ U)
    (habs : ∀ t ∈ rationalAffineHull δ, ∃ ε : ℝ, 0 < ε ∧ AffineMap.lineMap δ t ε ∈ U) :
    U ∈ 𝓝[(rationalAffineHull δ : Set (Fin s → ℝ))] δ := by
  classical
  obtain ⟨m, p, e, hind, -, hchar⟩ := exists_rational_frame δ
  let pR : Fin s → ℝ := fun j => (p j : ℝ)
  have hindR : LinearIndependent ℝ (fun i => fun j => (e i j : ℝ)) :=
    linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℝ) (v := e) |>.2 hind
  let Φlin : (Fin m → ℝ) →ₗ[ℝ] (Fin s → ℝ) :=
    Fintype.linearCombination ℝ (fun i j => (e i j : ℝ))
  have hΦinj : Function.Injective Φlin := hindR.fintypeLinearCombination_injective
  obtain ⟨Ψ, hΨ⟩ := Φlin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hΦinj)
  have hΨc : Continuous Ψ := LinearMap.continuous_of_finiteDimensional Ψ
  let φA : (Fin m → ℝ) →ᵃ[ℝ] (Fin s → ℝ) := Φlin.toAffineMap + AffineMap.const ℝ _ pR
  have hφA : ∀ σ, φA σ = Φlin σ + pR := fun σ => rfl
  have hchar' : ∀ x, x ∈ rationalAffineHull δ ↔ ∃ σ, x = φA σ := fun x => by
    rw [hchar]
    refine exists_congr fun σ => ?_
    rw [hφA]
    constructor <;> intro h <;> rw [h] <;> ext j <;>
      simp [Φlin, pR, Fintype.linearCombination_apply, add_comm]
  have hΨφ : ∀ σ, Ψ (φA σ - pR) = σ := fun σ => by
    rw [hφA, add_sub_cancel_right]; exact LinearMap.congr_fun hΨ σ
  obtain ⟨σ₀, hσ₀⟩ := (hchar' δ).1 (self_mem_rationalAffineHull δ)
  -- the problem in the parameter space `ℝ^m`
  set U' : Set (Fin m → ℝ) := φA ⁻¹' U with hU'def
  have hU' : Convex ℝ U' := hU.affine_preimage φA
  have habs' : ∀ σ, ∃ ε : ℝ, 0 < ε ∧ AffineMap.lineMap σ₀ σ ε ∈ U' := fun σ => by
    obtain ⟨ε, hε, h⟩ := habs (φA σ) ((hchar' _).2 ⟨σ, rfl⟩)
    exact ⟨ε, hε, by rw [hU'def, Set.mem_preimage, AffineMap.apply_lineMap, ← hσ₀]; exact h⟩
  have hσ₀U : σ₀ ∈ U' := by rw [hU'def, Set.mem_preimage, ← hσ₀]; exact hδ
  have hspan : affineSpan ℝ U' = ⊤ := by
    refine eq_top_iff.2 fun σ _ => ?_
    obtain ⟨ε, hε, h⟩ := habs' σ
    have := AffineMap.lineMap_mem (1 / ε) (subset_affineSpan ℝ U' hσ₀U) (subset_affineSpan ℝ U' h)
    convert this using 1
    rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module', add_sub_cancel_right,
      smul_smul, one_div, inv_mul_cancel₀ hε.ne', one_smul, sub_add_cancel]
  obtain ⟨y, hy⟩ := (hU'.interior_nonempty_iff_affineSpan_eq_top).2 hspan
  have hint : σ₀ ∈ interior U' := by
    obtain ⟨ε, hε, hz⟩ := habs' (σ₀ + (σ₀ - y))
    have hcomb := hU'.combo_interior_self_mem_interior hy hz (a := ε / (1 + ε)) (b := 1 / (1 + ε))
      (by positivity) (by positivity) (by field_simp; ring)
    convert hcomb using 1
    rw [AffineMap.lineMap_apply_module']
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  -- back to `W`
  have hO : {x | Ψ (x - pR) ∈ interior U'} ∈ 𝓝 δ := by
    refine (isOpen_interior.preimage (hΨc.comp (continuous_id.sub continuous_const))).mem_nhds ?_
    change Ψ (δ - pR) ∈ interior U'
    rw [hσ₀, hΨφ]; exact hint
  refine mem_of_superset (inter_mem (nhdsWithin_le_nhds hO) self_mem_nhdsWithin) ?_
  rintro x ⟨hx, hxW⟩
  obtain ⟨σ, rfl⟩ := (hchar' x).1 hxW
  have : σ ∈ U' := interior_subset (by simpa only [Set.mem_setOf_eq, hΨφ] using hx)
  exact this

/-- A rational vector killed by every rational relation of the family `w` lies in its span. -/
private theorem mem_span_of_forall_relation {ι κ : Type*} [Fintype ι] (w : κ → ι → ℚ)
    (y : ι → ℚ) (hy : ∀ c : ι → ℚ, (∀ v, ∑ i, c i * w v i = 0) → ∑ i, c i * y i = 0) :
    y ∈ Submodule.span ℚ (Set.range w) := by
  classical
  have hdot : ∀ (φ : Module.Dual ℚ (ι → ℚ)) (z : ι → ℚ),
      φ z = ∑ i, φ (Pi.single i 1) * z i := fun φ z => by
    rw [LinearMap.pi_apply_eq_sum_univ φ z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := Submodule.span ℚ (Set.range w)),
    Submodule.mem_dualCoannihilator]
  intro φ hφ
  rw [hdot]
  exact hy _ fun v => by
    rw [← hdot]
    exact (Submodule.mem_dualAnnihilator _).1 hφ _ (Submodule.subset_span ⟨v, rfl⟩)

/-- Casting to `ℝ` maps the rational span of `w` into the real span of its cast. -/
private theorem map_cast_mem_span {ι κ : Type*} (w : κ → ι → ℚ) {y : ι → ℚ}
    (hy : y ∈ Submodule.span ℚ (Set.range w)) :
    (fun i => (y i : ℝ)) ∈ Submodule.span ℝ (Set.range fun v i => (w v i : ℝ)) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, rfl⟩ := hz
    exact Submodule.subset_span ⟨v, rfl⟩
  | zero =>
    convert Submodule.zero_mem _ using 1
    ext
    simp
  | add a b _ _ ha hb =>
    convert Submodule.add_mem _ ha hb using 1
    ext
    simp
  | smul q a _ ha =>
    convert Submodule.smul_mem _ (q : ℝ) ha using 1
    ext
    simp [Rat.smul_def]

/-- The real affine span of finitely many rational divisors is cut out by rational affine
relations: a real divisor satisfying every rational relation of a point of the span lies in it. -/
private theorem mem_affineSpan_of_forall_relation {Y : Scheme.{0}} (VQ : Finset (QDivisor Y))
    {Δ Φ : RDivisor Y} (hΔ : Δ ∈ affineSpan ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))))
    (hΦ : ∀ (c : Mori.PrimeDivisor Y →₀ ℚ) (q : ℚ),
      (c.sum fun P cP => (cP : ℝ) * Δ.coeff P) = q → (c.sum fun P cP => (cP : ℝ) * Φ.coeff P) = q) :
    Φ ∈ affineSpan ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))) := by
  classical
  set R := QDivisor.toRDivisor (X := Y) with hRdef
  obtain ⟨v₀, hv₀⟩ : VQ.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    simp only [Finset.coe_empty, Set.image_empty, AffineSubspace.span_empty] at hΔ
    exact AffineSubspace.notMem_bot ℝ _ Δ hΔ
  have hRv₀ : R v₀ ∈ R '' (VQ : Set (QDivisor Y)) := Set.mem_image_of_mem R hv₀
  set Ssupp : Finset (Mori.PrimeDivisor Y) := Δ.support ∪ VQ.biUnion fun v => v.support
  have hRsupp : ∀ v ∈ VQ, (R v).support ⊆ Ssupp := fun v hv P hP => by
    have : v.coeff P ≠ 0 := fun h0 => Finsupp.mem_support_iff.1 hP (by
      change (R v).coeff P = 0
      rw [hRdef, QDivisor.coeff_toRDivisor, h0, Rat.cast_zero])
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨v, hv, Finsupp.mem_support_iff.2 this⟩)
  -- the support of `Φ` lies in that of `Δ`
  have hΦsupp : Φ.support ⊆ Δ.support := fun P hP => by
    by_contra h
    have h0 : Δ.coeff P = 0 := Finsupp.notMem_support_iff.1 h
    have := hΦ (Finsupp.single P 1) 0 (by rw [Finsupp.sum_single_index (by simp)]; simp [h0])
    rw [Finsupp.sum_single_index (by simp)] at this
    have h2 : Φ.coeff P = 0 := by simpa using this
    exact Finsupp.mem_support_iff.1 hP h2
  let ι := {P // P ∈ Ssupp}
  have hrel : ∀ (c : ι → ℚ) (D : RDivisor Y),
      ((∑ i : ι, Finsupp.single (i : Mori.PrimeDivisor Y) (c i)).sum fun P cP =>
        (cP : ℝ) * D.coeff P) = ∑ i : ι, (c i : ℝ) * D.coeff i := fun c D => by
    rw [← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
    exact Finset.sum_congr rfl fun i _ => Finsupp.sum_single_index (by simp)
  let lam : (ι → ℚ) → RDivisor Y →ₗ[ℝ] ℝ := fun c =>
    ∑ i : ι, (c i : ℝ) • Finsupp.lapply (i : Mori.PrimeDivisor Y)
  have hlam : ∀ c D, lam c D = ∑ i : ι, (c i : ℝ) * D.coeff i := fun c D => by
    simp [lam, DivisorWithCoeffs.coeff_apply]
  -- the rational system of the direction of the span
  let w : VQ → ι → ℚ := fun v i => v.1.coeff i - v₀.coeff i
  let Φsys : Set (ι → ℚ) := {c | ∀ v : VQ, ∑ i, c i * w v i = 0}
  let x : ι → ℝ := fun i => (Φ - R v₀).coeff i
  have hx : ∀ c ∈ Φsys, ∑ i, (c i : ℝ) * x i = 0 := by
    intro c hc
    have hker : vectorSpan ℝ (R '' (VQ : Set (QDivisor Y))) ≤ LinearMap.ker (lam c) := by
      rw [vectorSpan_eq_span_vsub_set_right ℝ hRv₀, Submodule.span_le]
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, hlam, hRdef,
        DivisorWithCoeffs.coeff_sub, QDivisor.coeff_toRDivisor]
      have h' : ((∑ i, c i * w ⟨v, hv⟩ i : ℚ) : ℝ) = 0 := by rw [hc ⟨v, hv⟩]; simp
      push_cast [w] at h'
      rw [← h']
    have hΔdir : Δ -ᵥ R v₀ ∈ vectorSpan ℝ (R '' (VQ : Set (QDivisor Y))) := by
      rw [← direction_affineSpan]
      exact AffineSubspace.vsub_mem_direction hΔ (subset_affineSpan ℝ _ hRv₀)
    have h1 : lam c Δ = lam c (R v₀) := by
      have := hker hΔdir
      rwa [LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero] at this
    set q : ℚ := ∑ i : ι, c i * v₀.coeff i with hqdef
    have hq : lam c (R v₀) = q := by
      rw [hlam, hqdef]
      push_cast
      simp [hRdef, QDivisor.coeff_toRDivisor]
    have h2 := hΦ (∑ i : ι, Finsupp.single (i : Mori.PrimeDivisor Y) (c i)) q
      (by rw [hrel, ← hlam, h1, hq])
    rw [hrel, ← hlam, ← hq] at h2
    have : ∑ i, (c i : ℝ) * x i = lam c Φ - lam c (R v₀) := by
      rw [hlam, hlam, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [x, DivisorWithCoeffs.coeff_sub]; ring
    rw [this, h2, sub_self]
  have hxspan := mem_span_rational_solutions Φsys x hx
  have hxW : x ∈ Submodule.span ℝ (Set.range fun v i => (w v i : ℝ)) := by
    refine Submodule.span_le.2 ?_ hxspan
    rintro _ ⟨y, hy, rfl⟩
    exact map_cast_mem_span w (mem_span_of_forall_relation w y hy)
  -- back to divisors
  let ℓ : (ι → ℝ) →ₗ[ℝ] RDivisor Y :=
    ∑ i : ι, LinearMap.smulRight (LinearMap.proj i) (Finsupp.single (i : Mori.PrimeDivisor Y) 1)
  have hℓ : ∀ D : RDivisor Y, D.support ⊆ Ssupp → ℓ (fun i => D.coeff i) = D := fun D hD => by
    simp only [ℓ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
    rw [Finset.sum_coe_sort Ssupp (fun P => D.coeff P • Finsupp.single P (1 : ℝ))]
    conv_rhs => rw [← Finsupp.sum_single D]
    rw [Finsupp.sum_of_support_subset D hD _ (fun _ _ => Finsupp.single_zero _)]
    exact Finset.sum_congr rfl fun P _ => Finsupp.smul_single_one _ _
  have hℓw : ∀ v : VQ, ℓ (fun i => (w v i : ℝ)) = R v - R v₀ := fun v => by
    rw [← hℓ (R v - R v₀) (Finsupp.support_sub.trans
      (Finset.union_subset (hRsupp v v.2) (hRsupp v₀ hv₀)))]
    congr 1
    ext i
    simp [w, hRdef, DivisorWithCoeffs.coeff_sub, QDivisor.coeff_toRDivisor]
  have hℓx : ℓ x = Φ - R v₀ := hℓ _ (Finsupp.support_sub.trans
    (Finset.union_subset (hΦsupp.trans Finset.subset_union_left) (hRsupp v₀ hv₀)))
  have hdir : Φ - R v₀ ∈ vectorSpan ℝ (R '' (VQ : Set (QDivisor Y))) := by
    rw [← hℓx]
    have : Submodule.map ℓ (Submodule.span ℝ (Set.range fun v i => (w v i : ℝ))) ≤
        vectorSpan ℝ (R '' (VQ : Set (QDivisor Y))) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨v, rfl⟩
      rw [hℓw]
      exact vsub_mem_vectorSpan ℝ (Set.mem_image_of_mem R v.2) hRv₀
    exact this (Submodule.mem_map_of_mem hxW)
  have := AffineSubspace.vadd_mem_of_mem_direction (by rwa [direction_affineSpan])
    (subset_affineSpan ℝ _ hRv₀)
  simpa [vadd_eq_add] using this

private theorem IsRatAffineFamily.eventually_mem_convexHull {Y : Scheme.{0}} {s : ℕ}
    {Γ : (Fin s → ℝ) → RDivisor Y} (hΓ : IsRatAffineFamily Γ) {VQ : Finset (QDivisor Y)}
    {δ : Fin s → ℝ} (hΔ : Γ δ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))))
    (hrel : ∀ x ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))), ∃ ε : ℝ,
      0 < ε ∧ Γ δ + ε • (Γ δ - x) ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y)))) :
    ∀ᶠ t in 𝓝[(rationalAffineHull δ : Set (Fin s → ℝ))] δ,
      Γ t ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))) := by
  obtain ⟨LΓ, hLΓ⟩ := hΓ.exists_affineMap
  have hconv := convex_convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y)))
  have hU := mem_nhdsWithin_rationalAffineHull_of_convex
    (U := LΓ ⁻¹' convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))))
    (hconv.affine_preimage LΓ) (by simpa [hLΓ] using hΔ) fun t ht => by
      have hspan : Γ t ∈ affineSpan ℝ
          (convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y)))) := by
        rw [affineSpan_convexHull]
        exact mem_affineSpan_of_forall_relation VQ (convexHull_subset_affineSpan _ hΔ)
          fun c q hc => hΓ.relation ht c q hc
      obtain ⟨ε, hε, hmem⟩ := exists_lineMap_mem_of_mem_affineSpan hconv hΔ hrel hspan
      exact ⟨ε, hε, by rwa [Set.mem_preimage, AffineMap.apply_lineMap, hLΓ, hLΓ]⟩
  filter_upwards [hU] with t ht
  simpa [hLΓ] using ht

end Convex

-- Divisor bookkeeping

section Bookkeeping

variable {X Y : Scheme.{0}}

private theorem toRDivisor_single (P : Mori.PrimeDivisor X) (r : ℤ) :
    Divisor.toRDivisor (Finsupp.single P r) = Finsupp.single P (r : ℝ) := by
  classical
  ext E
  rw [Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
    Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

/-- The birational transform commutes with regarding an integral divisor as a real one. -/
private theorem toRDivisor_transformDivisor (φ : X.RationalMap Y) (D : Divisor X) :
    Divisor.toRDivisor (RationalMap.transformDivisor φ D) =
      RationalMap.transformDivisor φ (Divisor.toRDivisor D) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add D D' h h' => simp only [map_add, h, h']
  | single P r =>
    rw [toRDivisor_single, RationalMap.transformDivisor_single,
      RationalMap.transformDivisor_single]
    cases RationalMap.transformPrimeDivisor φ P with
    | none => exact map_zero _
    | some E => exact toRDivisor_single E r

private theorem transformDivisor_smul (φ : X.RationalMap Y) (c : ℝ) (D : RDivisor X) :
    RationalMap.transformDivisor φ (c • D) = c • RationalMap.transformDivisor φ D :=
  (RationalMap.transformDivisorₗ ℝ φ).map_smul c D

private theorem support_subset_of_toRDivisor_zsmul_eq {C : Divisor X} {D : RDivisor X}
    {S : Finset (Mori.PrimeDivisor X)} {m : ℕ} (hm : m ≠ 0) (c : ℝ)
    (h : Divisor.toRDivisor ((m : ℤ) • C) = c • D) (hD : D.support ⊆ S) : C.support ⊆ S := by
  intro P hP
  by_contra hPS
  have h1 := congrArg (fun D : RDivisor X => D.coeff P) h
  have h2 : D.coeff P = 0 := by
    by_contra h0
    exact hPS (hD (Finsupp.mem_support_iff.2 h0))
  simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, h2, smul_zero, smul_eq_mul,
    mul_zero, Int.cast_mul, Int.cast_natCast, mul_eq_zero, Nat.cast_eq_zero, Int.cast_eq_zero] at h1
  exact h1.elim hm (Finsupp.mem_support_iff.1 hP)

private theorem isRCartier_of_isRCartierPullback [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {D : RDivisor X} {G : RDivisor Y}
    (h : MMP.Flips.IsRCartierPullback f D G) : RDivisor.IsRCartier D := by
  obtain ⟨m, r, L, L', hL, rfl, -, -⟩ := h
  exact ⟨m, r, L, hL, fun P => coeff_sum_smul_toRDivisor r L P⟩

/-- On a scheme on which every Weil divisor has a Cartier multiple, one positive integer makes
every divisor supported in a fixed finite set Cartier. -/
private theorem exists_zsmul_isCartier [IsLocallyNoetherian X] [IsNormal X]
    (hQ : ∀ D : Divisor X, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier)
    (S : Finset (Mori.PrimeDivisor X)) :
    ∃ e : ℕ, 0 < e ∧ ∀ C : Divisor X, C.support ⊆ S → ((e : ℤ) • C).IsCartier := by
  classical
  choose m hm hmC using fun P : Mori.PrimeDivisor X => hQ (Finsupp.single P 1)
  refine ⟨∏ P ∈ S, m P, Finset.prod_pos fun P _ => hm P, fun C hC => ?_⟩
  have hCsum : C = ∑ P ∈ S, C P • Finsupp.single P 1 := by
    conv_lhs => rw [← Finsupp.sum_single C]
    rw [Finsupp.sum_of_support_subset C hC _ (fun _ _ => Finsupp.single_zero _)]
    exact Finset.sum_congr rfl fun P _ => (Finsupp.smul_single_one _ _).symm
  have hterm : ∀ P ∈ S, ((∏ Q ∈ S, m Q : ℕ) : ℤ) • (C P • Finsupp.single P (1 : ℤ)) =
      (C P * ∏ Q ∈ S.erase P, (m Q : ℤ)) • ((m P : ℤ) • Finsupp.single P 1) := fun P hP => by
    rw [smul_smul, smul_smul, ← Finset.mul_prod_erase S m hP]
    congr 1
    push_cast
    ring
  have hsum : ∀ (I : Finset (Mori.PrimeDivisor X)) (g : Mori.PrimeDivisor X → ℤ),
      Divisor.IsCartier (∑ P ∈ I, g P • ((m P : ℤ) • (Finsupp.single P 1 : Divisor X))) := by
    intro I g
    induction I using Finset.induction_on with
    | empty => simpa using Divisor.isCartier_zero
    | insert P I hP ih =>
      rw [Finset.sum_insert hP]
      exact ((hmC P).zsmul _).add ih
  rw [hCsum, Finset.smul_sum, Finset.sum_congr rfl hterm]
  exact hsum S _

end Bookkeeping

-- Uniform freeness on `Y`

section Freeness

variable {Y Z : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- On a klt pair every boundary coefficient is `< 1`: the log discrepancy `1 - b_P` of a prime
divisor `P` of `Y` is positive. -/
private theorem coeff_lt_one_of_isKltPair {Θ : QDivisor Y} (hΘ : IsKltPair sY Θ)
    (P : MMP.Mori.PrimeDivisor Y) : Θ.coeff P < 1 := by
  obtain ⟨hvar, n, K, hK, -⟩ := id hΘ.1.isPair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΘ.1.isPair hK
    (DivisorOver.ofPrimeDivisor ℂ hvar P)
  have hp : IsProper (DivisorOver.ofPrimeDivisor ℂ hvar P).f := by
    change IsProper (𝟙 Y)
    infer_instance
  have h := hΘ.2 n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hp)
  rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hvar ha] at h
  push_cast at h
  exact_mod_cast (by linarith : ((Θ.coeff P : ℚ) : ℝ) < 1)

/-- The coefficients of `∑ᵢ xᵢ Pᵢ` for distinct primes `Pᵢ`. -/
private theorem coeff_sum_single_of_injective {R : Type*} [AddCommMonoid R] {r : ℕ}
    {pr : Fin r → MMP.Mori.PrimeDivisor Y} (hpr : Function.Injective pr) (x : Fin r → R) :
    (∀ j, DivisorWithCoeffs.coeff (∑ i, Finsupp.single (pr i) (x i)) (pr j) = x j) ∧
      ∀ P, P ∉ Set.range pr → DivisorWithCoeffs.coeff (∑ i, Finsupp.single (pr i) (x i)) P = 0 := by
  classical
  refine ⟨fun j => ?_, fun P hP => ?_⟩
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply,
      Finset.sum_eq_single j (fun i _ hij => Finsupp.single_eq_of_ne' (hpr.ne hij))
        (fun h => absurd (Finset.mem_univ j) h), Finsupp.single_eq_same]
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
    exact Finset.sum_eq_zero fun i _ => Finsupp.single_eq_of_ne' fun h => hP ⟨i, h⟩

private theorem toRDivisor_sum_single_of_injective {r : ℕ} {pr : Fin r → MMP.Mori.PrimeDivisor Y}
    (hpr : Function.Injective pr) (v : Fin r → ℚ) :
    (∑ i, Finsupp.single (pr i) (v i : ℝ) : RDivisor Y) =
      QDivisor.toRDivisor (∑ i, Finsupp.single (pr i) (v i)) := by
  ext P
  change DivisorWithCoeffs.coeff (∑ i, Finsupp.single (pr i) (v i : ℝ)) P =
    (QDivisor.toRDivisor (∑ i, Finsupp.single (pr i) (v i))).coeff P
  rw [QDivisor.coeff_toRDivisor]
  by_cases hP : P ∈ Set.range pr
  · obtain ⟨j, rfl⟩ := hP
    rw [(coeff_sum_single_of_injective hpr _).1 j, (coeff_sum_single_of_injective hpr v).1 j]
  · rw [(coeff_sum_single_of_injective hpr _).2 P hP,
      (coeff_sum_single_of_injective hpr v).2 P hP, Rat.cast_zero]

private theorem sum_single_coeff_of_injective {r : ℕ} {pr : Fin r → MMP.Mori.PrimeDivisor Y}
    (hpr : Function.Injective pr) {Δ : RDivisor Y}
    (hΔ : ∀ P, P ∉ Set.range pr → Δ.coeff P = 0) :
    (∑ i, Finsupp.single (pr i) (Δ.coeff (pr i)) : RDivisor Y) = Δ := by
  ext P
  change DivisorWithCoeffs.coeff (∑ i, Finsupp.single (pr i) (Δ.coeff (pr i))) P = Δ.coeff P
  by_cases hP : P ∈ Set.range pr
  · obtain ⟨j, rfl⟩ := hP
    rw [(coeff_sum_single_of_injective hpr _).1 j]
  · rw [(coeff_sum_single_of_injective hpr _).2 P hP, hΔ P hP]

/-- The uniform freeness theorem, applied to a rational klt polytope around a real klt
boundary `Δ` containing a relatively big `G`. -/
private theorem exists_uniform_freeness (hYQ : IsQFactorial sY)
    (hYp : Mori.IsProjectiveVariety ℂ sY) (hZp : Mori.IsProjectiveVariety ℂ sZ)
    (fY : Y ⟶ Z) (hfY : fY ≫ sZ = sY) {KY : Divisor Y}
    (hKY : ∃ m : ℕ, KY.IsCanonicalDivisor sY m) {Δ : RDivisor Y} (hΔ0 : 0 ≤ Δ)
    (hΔklt : IsRealKltPair sY Δ) {G : QDivisor Y} (hG0 : 0 ≤ G) (hGbig : G.IsRelativelyBig fY)
    (hGΔ : QDivisor.toRDivisor G ≤ Δ)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sY fY (Divisor.toRDivisor KY + Δ)) :
    ∃ VQ : Finset (QDivisor Y),
      Δ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))) ∧
      (∀ Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))), ∃ ε : ℝ, 0 < ε ∧
          Δ + ε • (Δ - Γ) ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y)))) ∧
      (∃ b : ℕ, 0 < b ∧
        ∀ Γ ∈ convexHull ℝ (QDivisor.toRDivisor '' (VQ : Set (QDivisor Y))), ∀ c : ℝ, 0 < c →
          ∀ D : Divisor Y, D.IsCartier → c • (Divisor.toRDivisor KY + Γ) = Divisor.toRDivisor D →
            IsRelativelyFreeDivisor fY ((b : ℤ) • D)) ∧
      ∃ H : Finset (Divisor Y),
        (∀ h ∈ H, h.IsCartier ∧ ∃ p : ℕ, 0 < p ∧ IsRelativelyFreeDivisor fY ((p : ℤ) • h)) ∧
        ∃ t : Divisor Y → ℝ, (∀ h, 0 ≤ t h) ∧
            Divisor.toRDivisor KY + Δ = ∑ h ∈ H, t h • Divisor.toRDivisor h := by
  classical
  have : AlgebraicGeometry.IsProjectiveVariety ℂ sY := hYp
  have : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZp
  -- coordinates on the primes of the supports of `Δ` and `G`
  set S : Finset (Mori.PrimeDivisor Y) := Δ.support ∪ G.support with hSdef
  let pr : Fin S.card → Mori.PrimeDivisor Y := fun i => (S.equivFin.symm i : Mori.PrimeDivisor Y)
  have hpr : Function.Injective pr := Subtype.val_injective.comp S.equivFin.symm.injective
  have hprS : ∀ P ∈ S, P ∈ Set.range pr := fun P hP => ⟨S.equivFin ⟨P, hP⟩, by simp [pr]⟩
  have hGS : ∀ P, P ∉ Set.range pr → G.coeff P = 0 := fun P hP => by
    by_contra h
    exact hP (hprS P (Finset.mem_union_right _ (Finsupp.mem_support_iff.2 h)))
  have hΔS : ∀ P, P ∉ Set.range pr → Δ.coeff P = 0 := fun P hP => by
    by_contra h
    exact hP (hprS P (Finset.mem_union_left _ (Finsupp.mem_support_iff.2 h)))
  obtain ⟨V, -, hint, hVG, hVklt⟩ := exists_rationalPolytope_isKltPair_of_isRealKltPair sY hYp
    hYQ Δ hΔ0 hΔklt G hG0 hGΔ pr hpr
    (fun P hP => by_contra fun h => hP (hΔS P h)) (fun P hP => by_contra fun h => hP (hGS P h))
  -- the vertices as `ℚ`-divisors
  let toQ : (Fin S.card → ℚ) → QDivisor Y := fun v => ∑ i, Finsupp.single (pr i) (v i)
  have hGv : ∀ v ∈ V, ∀ i, G.coeff (pr i) ≤ v i := fun v hv i => by
    have := hVG _ (subset_convexHull ℝ _ ⟨v, hv, rfl⟩) i
    simp only at this
    exact_mod_cast this
  let V0 := V.image toQ
  have hV0 : ∀ Γ ∈ V0, ∃ v ∈ V, Γ = toQ v := fun Γ hΓ => by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hΓ
    exact ⟨v, hv, rfl⟩
  have hV0G : ∀ Γ ∈ V0, G ≤ Γ := fun Γ hΓ P => by
    obtain ⟨v, hv, rfl⟩ := hV0 Γ hΓ
    by_cases hP : P ∈ Set.range pr
    · obtain ⟨i, rfl⟩ := hP
      change G.coeff (pr i) ≤ (toQ v).coeff (pr i)
      rw [(coeff_sum_single_of_injective hpr v).1 i]
      exact hGv v hv i
    · change G.coeff P ≤ (toQ v).coeff P
      rw [hGS P hP, (coeff_sum_single_of_injective hpr v).2 P hP]
  have hV0klt : ∀ Γ ∈ V0, IsKltPair sY Γ := fun Γ hΓ => by
    obtain ⟨v, hv, rfl⟩ := hV0 Γ hΓ
    exact hVklt v hv
  have hV0eff : ∀ Γ ∈ V0, Γ.IsEffective := fun Γ hΓ E => (hG0 E).trans (hV0G Γ hΓ E)
  have hV0le : ∀ Γ ∈ V0, ∀ E, Γ.coeff E ≤ 1 := fun Γ hΓ E =>
    (coeff_lt_one_of_isKltPair (hV0klt Γ hΓ) E).le
  -- `Δ` lies in the convex hull of the vertices
  let Lm : (Fin S.card → ℝ) →ₗ[ℝ] RDivisor Y :=
    ∑ i, LinearMap.smulRight (LinearMap.proj i) (Finsupp.single (pr i) (1 : ℝ))
  have hLm : ∀ x, Lm x = ∑ i, Finsupp.single (pr i) (x i) := fun x => by
    simp only [Lm, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
    exact Finset.sum_congr rfl fun i _ => Finsupp.smul_single_one _ _
  have hLmv : ∀ v, Lm (fun i => (v i : ℝ)) = QDivisor.toRDivisor (toQ v) := fun v =>
    (hLm _).trans (toRDivisor_sum_single_of_injective hpr v)
  have hLmΔ : Lm (fun i => Δ.coeff (pr i)) = Δ :=
    (hLm _).trans (sum_single_coeff_of_injective hpr hΔS)
  have hΔconv : Δ ∈ convexHull ℝ (QDivisor.toRDivisor '' (V0 : Set (QDivisor Y))) := by
    have : Δ ∈ Lm '' convexHull ℝ ((fun v i => (v i : ℝ)) '' (V : Set (Fin S.card → ℚ))) :=
      ⟨_, intrinsicInterior_subset hint, hLmΔ⟩
    rw [LinearMap.image_convexHull, Set.image_image] at this
    convert this using 2
    ext D
    simp only [V0, Finset.coe_image, Set.mem_image, exists_exists_and_eq_and, hLmv]
  obtain ⟨VQ, -, -, hΔVQ, hrel, hb, H, hH, hcone⟩ :=
    QDivisor.IsRelativelyBig.exists_isRelativelyFreeDivisor_nsmul_of_isRelativelyNef sY sZ hYQ
      fY hfY hKY hGbig hG0 V0 hV0eff hV0le hV0G hV0klt hΔconv hnef
  exact ⟨VQ, hΔVQ, hrel, hb, H, hH, hcone Δ hΔVQ⟩

/-- If `(e b) C' = k (K_Y + Γ)` and `b D` is relatively free whenever `D` is Cartier and a
positive multiple of `K_Y + Γ`, then `(e b) C'` is Cartier and relatively free as soon as
`e C'` is Cartier. -/
private theorem isCartier_and_isRelativelyFreeDivisor_mul_zsmul {fY : Y ⟶ Z} {KY : Divisor Y}
    {Γ : RDivisor Y} {C' : Divisor Y} {e bb k : ℕ} (hbb : 0 < bb) (hk : 0 < k)
    (hfree : ∀ c : ℝ, 0 < c → ∀ D : Divisor Y, D.IsCartier →
      c • (Divisor.toRDivisor KY + Γ) = Divisor.toRDivisor D →
        IsRelativelyFreeDivisor fY ((bb : ℤ) • D))
    (hCe : ((e : ℤ) • C').IsCartier)
    (hC'k : Divisor.toRDivisor (((e * bb : ℕ) : ℤ) • C') =
      (k : ℝ) • (Divisor.toRDivisor KY + Γ)) :
    (((e * bb : ℕ) : ℤ) • C').IsCartier ∧ IsRelativelyFreeDivisor fY (((e * bb : ℕ) : ℤ) • C') := by
  have hbb' : (bb : ℝ) ≠ 0 := by exact_mod_cast hbb.ne'
  have hmul : (((e * bb : ℕ) : ℤ) • C') = (bb : ℤ) • ((e : ℤ) • C') := by
    rw [smul_smul]
    push_cast
    ring_nf
  refine ⟨hmul ▸ hCe.zsmul _, hmul ▸ hfree ((k : ℝ) / bb) (by positivity) _ hCe ?_⟩
  ext P
  have h1 := congrArg (fun D : RDivisor Y => D.coeff P) hC'k
  change (((k : ℝ) / bb) • (Divisor.toRDivisor KY + Γ)).coeff P =
    (Divisor.toRDivisor ((e : ℤ) • C')).coeff P
  simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul] at h1 ⊢
  push_cast at h1 ⊢
  rw [div_mul_eq_mul_div, ← h1]
  field_simp

end Freeness

-- Fixed parts on the common model

section CommonModel

variable {k : Type} [Field k] {X Y T Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
  [IsIntegral X] [IsIntegral Y] [IsIntegral T]
  [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
  [IsLocallyNoetherian T] [IsNormal T] [CompactSpace X] [CompactSpace Y] [CompactSpace T]

/-- Let `p : T ⟶ X`, `q : T ⟶ Y` be a common model over `Z`, and let `E = p^*D - q^*D'` be
effective with `q_*E = 0`. If `C` is an integral Cartier divisor with `C = c • D` whose
counterpart `C' = c • D'` on `Y` is Cartier and relatively free, then every fixed component of
`C` over `Z` is a component of `p_*E`. -/
private theorem pos_transformDivisor_of_pos_relativeFixedMultiplicity
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) (hT : IsNormalVariety k sT)
    (hZ : Mori.IsVariety k sZ) (p : T ⟶ X) (q : T ⟶ Y) (fX : X ⟶ Z) (fY : Y ⟶ Z)
    [IsProper p] [IsProper q] (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q)
    (hpX : p ≫ sX = sT) (hqY : q ≫ sY = sT) (hfX : fX ≫ sZ = sX) (hfY : fY ≫ sZ = sY)
    (hZc : p ≫ fX = q ≫ fY) {D : RDivisor X} {D' : RDivisor Y} {PD QD : RDivisor T}
    (hPD : MMP.Flips.IsRCartierPullback p D PD) (hQD : MMP.Flips.IsRCartierPullback q D' QD)
    (hE0 : 0 ≤ PD - QD)
    (hqE : RationalMap.transformDivisor (X := T) q.toRationalMap (PD - QD) = 0)
    {c : ℝ} (hc : 0 < c) {C : Divisor X} (hC : C.IsCartier)
    (hCD : Divisor.toRDivisor C = c • D) {C' : Divisor Y} (hC' : C'.IsCartier)
    (hC'D : Divisor.toRDivisor C' = c • D') (hfree : IsRelativelyFreeDivisor fY C')
    {F : Mori.PrimeDivisor X} (hF : 0 < relativeFixedMultiplicity fX C F) :
    0 < (RationalMap.transformDivisor (X := T) p.toRationalMap (PD - QD)).coeff F := by
  have := hp.isDominant
  have := hq.isDominant
  have hB := map_componentGenericPoint_notMem_supp_of_isDominant p C
  have hB' := map_componentGenericPoint_notMem_supp_of_isDominant q C'
  set E : Divisor T := C.pullback hC hB - C'.pullback hC' hB' with hEdef
  have hEk : Divisor.toRDivisor E = c • (PD - QD) := by
    rw [hEdef, map_sub, smul_sub,
      MMP.Flips.IsRCartierPullback.eq p
        (isRCartierPullback_toRDivisor hC hB (Divisor.isPullback_pullback hC hB))
        (hCD ▸ isRCartierPullback_smul c hPD),
      MMP.Flips.IsRCartierPullback.eq q
        (isRCartierPullback_toRDivisor hC' hB' (Divisor.isPullback_pullback hC' hB'))
        (hC'D ▸ isRCartierPullback_smul c hQD)]
  have hE0' : 0 ≤ E := fun G => by
    have h := congrArg (fun D : RDivisor T => D.coeff G) hEk
    simp only [Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h
    have : (0 : ℝ) ≤ E.coeff G := h ▸ mul_nonneg hc.le (hE0 G)
    exact_mod_cast this
  have hqE' : RationalMap.transformDivisor (X := T) q.toRationalMap E = 0 := by
    apply MMP.Mori.Divisor.toRDivisor_injective
    rw [map_zero, toRDivisor_transformDivisor, hEk, transformDivisor_smul, hqE, smul_zero]
  obtain ⟨m, hm1, hm2⟩ := (sections_and_fixed_part_of_pullback_eq_add hX hY hT hZ p q fX fY hp
    hq hpX hqY hfX hfY hZc hC hC' hE0' hqE' ⟨hB, hB', by rw [hEdef]; abel⟩).2 hfree F
  have h := congrArg (fun D : RDivisor X => D.coeff F)
    (toRDivisor_transformDivisor p.toRationalMap E)
  simp only [Divisor.coeff_toRDivisor, hm1, hEk, transformDivisor_smul,
    DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h
  rw [hm2] at hF
  have hm : (0 : ℝ) < m := by exact_mod_cast hF
  exact pos_of_mul_pos_right (by rwa [← Int.cast_natCast, h] at hm) hc.le

end CommonModel

variable {X Y T Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
  {sT : T ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
  [IsIntegral X] [IsIntegral Y] [IsIntegral T]
  [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
  [IsLocallyNoetherian T] [IsNormal T] [CompactSpace X] [CompactSpace Y] [CompactSpace T]

/-- **Fixed-part uniformity from one big-boundary model.** Let `φ : X ⤏ Y` be a birational
contraction over a projective complex variety `Z` (structure maps `fX`, `fY`) of `ℚ`-factorial
normal projective varieties, and `p : T ⟶ X`, `q : T ⟶ Y` a common projective birational model
(`p⁻¹` followed by `q` is `φ`). Let `D_t` be a rational affine family of `ℝ`-Cartier divisors on
`X` with fixed finite support, `t` in a rational affine subspace `V ⊆ ℝ^s`, with
`φ_* D_t = K_Y + Γ_t` for a rational affine family `Γ_t`, and let `P t = p^*D_t`,
`Q t = q^*φ_*D_t` with `q_*(P t - Q t) = 0`. Fix `δ ∈ V` such that `Γ_δ` is an effective real klt
boundary containing an effective `ℚ`-divisor `G` big over `Z`, `P δ - Q δ ≥ 0` and `K_Y + Γ_δ` is
nef over `Z`. Then

* every prime of the relative divisorial stable base locus of `D_δ` lies in that of `D_t` for
  all `t ∈ V` near `δ`;
* there is `r > 0` such that for all `t` near `δ` in `rationalAffineHull δ`, every `k > 0` and
  every integral Cartier `C` with `r C = k D_t`, every component of the relative fixed part of
  `k D_t = r C` lies in the relative divisorial stable base locus of `D_δ`. -/
@[mmp "prop_fourfold_one_model_fixed_part_uniformity"]
public theorem isInRelativeDivisorialStableBase_uniformity_of_isBirationalContraction
    (hXQ : IsQFactorial sX) (hXp : Mori.IsProjectiveVariety ℂ sX)
    (hYQ : IsQFactorial sY) (hYp : Mori.IsProjectiveVariety ℂ sY)
    (hZp : Mori.IsProjectiveVariety ℂ sZ) (hT : IsNormalVariety ℂ sT)
    (fX : X ⟶ Z) (fY : Y ⟶ Z) (hfX : fX ≫ sZ = sX) (hfY : fY ≫ sZ = sY)
    (φ : X.RationalMap Y) (hφ : Mori.RationalMap.IsBirational φ)
    (hover : MMP.Flips.RationalMap.IsOver fX fY φ)
    (hcontr : ∀ F : Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (p : T ⟶ X) (q : T ⟶ Y) (hpproj : IsProjectiveMorphism p)
    (hqproj : IsProjectiveMorphism q)
    (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q)
    (hpX : p ≫ sX = sT) (hqY : q ≫ sY = sT)
    (h : X.RationalMap T) (hh : Mori.RationalMap.IsInverse p.toRationalMap h)
    (hhq : h.compHom q = φ)
    {s : ℕ} {V : Set (Fin s → ℝ)} (hV : IsRationalAffineSubspace V)
    (D : (Fin s → ℝ) → RDivisor X) {n : ℕ} (PX : Fin n → Mori.PrimeDivisor X)
    (a : Fin n → (Fin s → ℚ) × ℚ) (hDcoeff : ∀ t i, (D t).coeff (PX i) = ratAffineForm (a i) t)
    (hDsupp : ∀ t, ↑(D t).support ⊆ Set.range PX)
    (hDc : ∀ t ∈ V, RDivisor.IsRCartier (D t))
    (KY : Divisor Y) (hKY : ∃ m : ℕ, KY.IsCanonicalDivisor sY m)
    (Γ : (Fin s → ℝ) → RDivisor Y) {n' : ℕ} (PY : Fin n' → Mori.PrimeDivisor Y)
    (b : Fin n' → (Fin s → ℚ) × ℚ) (hΓcoeff : ∀ t i, (Γ t).coeff (PY i) = ratAffineForm (b i) t)
    (hΓsupp : ∀ t, ↑(Γ t).support ⊆ Set.range PY)
    (hD' : ∀ t ∈ V, RationalMap.transformDivisor φ (D t) = Divisor.toRDivisor KY + Γ t)
    (P Q : (Fin s → ℝ) → RDivisor T)
    (hP : ∀ t ∈ V, MMP.Flips.IsRCartierPullback p (D t) (P t))
    (hQ : ∀ t ∈ V, MMP.Flips.IsRCartierPullback q (Divisor.toRDivisor KY + Γ t) (Q t))
    (hqE : ∀ t ∈ V, RationalMap.transformDivisor (X := T) q.toRationalMap (P t - Q t) = 0)
    {δ : Fin s → ℝ} (hδV : δ ∈ V)
    (hΓ0 : 0 ≤ Γ δ) (hΓklt : IsRealKltPair sY (Γ δ))
    (G : QDivisor Y) (hG0 : 0 ≤ G) (hGbig : G.IsRelativelyBig fY)
    (hGΓ : QDivisor.toRDivisor G ≤ Γ δ)
    (hEδ : 0 ≤ P δ - Q δ)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sY fY (Divisor.toRDivisor KY + Γ δ)) :
    (∀ᶠ t in 𝓝[V] δ, ∀ F : Mori.PrimeDivisor X,
      IsInRelativeDivisorialStableBase fX (D δ) F → IsInRelativeDivisorialStableBase fX (D t) F) ∧
    ∃ r : ℕ, 0 < r ∧ ∀ᶠ t in 𝓝[(rationalAffineHull δ : Set (Fin s → ℝ))] δ,
      ∀ k : ℕ, 0 < k → ∀ C : Divisor X, C.IsCartier →
        Divisor.toRDivisor ((r : ℤ) • C) = (k : ℝ) • D t →
          ∀ F : Mori.PrimeDivisor X, 0 < relativeFixedMultiplicity fX ((r : ℤ) • C) F →
            IsInRelativeDivisorialStableBase fX (D δ) F := by
  classical
  have := hp.isDominant
  have := hq.isDominant
  have : IsProper p := isProper_of_isProjectiveMorphism p hpproj
  have : IsProper q := isProper_of_isProjectiveMorphism q hqproj
  have hX : IsNormalVariety ℂ sX := hXQ.1
  have hY : IsNormalVariety ℂ sY := hYQ.1
  have hZ : Mori.IsVariety ℂ sZ := hZp.toIsVariety
  have : IsSeparated sZ := hZ.toIsSeparated
  have hZc : p ≫ fX = q ≫ fY := comp_eq_comp_of_isOver_of_comp_eq sZ fX fY hover p q hh hhq
    (by rw [Category.assoc, Category.assoc, hfX, hfY, hpX, hqY])
  have hTX : IsNormalVariety ℂ (p ≫ sX) := hpX ▸ hT
  have hDfam : IsRatAffineFamily D := isRatAffineFamily_of_coeff D PX a hDcoeff hDsupp
  have hΓfam : IsRatAffineFamily Γ := isRatAffineFamily_of_coeff Γ PY b hΓcoeff hΓsupp
  have hD'fam : IsRatAffineFamily (fun t => Divisor.toRDivisor KY + Γ t) := hΓfam.const_add KY
  obtain ⟨VQ, hΔVQ, hVQrel, ⟨bb, hbb, hfree⟩, H, hH, c, hc, hcH⟩ :=
    exists_uniform_freeness hYQ hYp hZp fY hfY hKY hΓ0 hΓklt hG0 hGbig hGΓ hnef
  -- the stable base primes of `D δ` are the positive components of `p_* E_δ`
  have hbase : ∀ F, IsInRelativeDivisorialStableBase fX (D δ) F →
      0 < (RationalMap.transformDivisor (X := T) p.toRationalMap (P δ - Q δ)).coeff F := by
    intro F hF
    choose hHc pp hpp hppfree using hH
    let e := H.equivFin
    refine (isInRelativeDivisorialStableBase_iff_pos_transformDivisor hX hY hT p q fX fY hp hq
      hpX hqY hZc (hP δ hδV) (hQ δ hδV) (add_sub_cancel _ _).symm hEδ (hqE δ hδV)
      (fun i => c (e.symm i).1 / pp _ (e.symm i).2)
      (fun i => div_nonneg (hc _) (Nat.cast_nonneg _))
      (fun i => ((pp _ (e.symm i).2 : ℕ) : ℤ) • (e.symm i).1)
      (fun i => (hHc _ (e.symm i).2).zsmul _) (fun i => hppfree _ _)
      (s₀ := 0) Fin.elim0 Fin.elim0 ?_ F).1 hF
    rw [hcH, Fin.sum_univ_zero, add_zero, ← Finset.sum_coe_sort H,
      ← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp0 : (pp _ (e.symm i).2 : ℝ) ≠ 0 := by exact_mod_cast (hpp _ (e.symm i).2).ne'
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    congr 1
    push_cast
    field_simp
  refine ⟨?_, ?_⟩
  · -- persistence of the stable base primes, on `V` viewed as an affine space
    obtain ⟨LD, hLD⟩ := hDfam.exists_affineMap
    obtain ⟨LD', hLD'⟩ := hD'fam.exists_affineMap
    obtain ⟨SX, hSX⟩ := hDfam.exists_finset
    obtain ⟨SY, hSY⟩ := hD'fam.exists_finset
    obtain ⟨Fs, hFs⟩ := hV
    let A : AffineSubspace ℝ (Fin s → ℝ) :=
      { carrier := V
        smul_vsub_vadd_mem' := fun c p₁ p₂ p₃ h₁ h₂ h₃ => by
          rw [hFs] at h₁ h₂ h₃ ⊢
          intro f hf
          simp only [vsub_eq_sub, vadd_eq_add]
          rw [ratAffineForm_affine, h₁ f hf, h₂ f hf, h₃ f hf]
          ring }
    have : Nonempty A := ⟨⟨δ, hδV⟩⟩
    have key := eventually_isInRelativeDivisorialStableBase_of_coeff_pos (k := ℂ) hX hY hT hZ
      p q fX fY hp hq hpX hqY hfX hfY hZc (LD.comp A.subtype) (LD'.comp A.subtype)
      (fun t => by simpa [hLD] using hDc t.1 t.2)
      (fun t => by simpa [hLD'] using isRCartier_of_isRCartierPullback (hQ t.1 t.2))
      ⟨SX, fun t => by simpa [hLD] using hSX t.1⟩ ⟨SY, fun t => by simpa [hLD'] using hSY t.1⟩
      (fun t => P t.1) (fun t => Q t.1) (fun t => by simpa [hLD] using hP t.1 t.2)
      (fun t => by simpa [hLD'] using hQ t.1 t.2) (fun t => hqE t.1 t.2) ⟨δ, hδV⟩
    have key' : ∀ᶠ t in 𝓝[V] δ, ∀ F : Mori.PrimeDivisor X,
        0 < (RationalMap.transformDivisor p.toRationalMap (P δ - Q δ)).coeff F →
          IsInRelativeDivisorialStableBase fX (D t) F := by
      rw [nhdsWithin_eq_map_subtype_coe hδV, eventually_map]
      filter_upwards [key] with t ht F hF
      simpa [hLD] using ht F hF
    filter_upwards [key'] with t ht F hF
    exact ht F (hbase F hF)
  · -- the comparison family `E_t` on the common model
    obtain ⟨GP, hGPfam, hGP⟩ := hDfam.exists_isRCartierPullback hXQ.2 p
    obtain ⟨GQ, hGQfam, hGQ⟩ := hD'fam.exists_isRCartierPullback hYQ.2 q
    have hPV : ∀ t ∈ V, P t = GP t := fun t ht =>
      MMP.Flips.IsRCartierPullback.eq p (hP t ht) (hGP t)
    have hQV : ∀ t ∈ V, Q t = GQ t := fun t ht =>
      MMP.Flips.IsRCartierPullback.eq q (hQ t ht) (hGQ t)
    have hEδ' : 0 ≤ GP δ - GQ δ := by simpa only [← hPV δ hδV, ← hQV δ hδV] using hEδ
    obtain ⟨hWV, hEev⟩ := (hGPfam.sub hGQfam).eventually_nonneg hV hδV hEδ'
    have hΓev := hΓfam.eventually_mem_convexHull hΔVQ hVQrel
    -- a uniform Cartier index for the push-forwards
    obtain ⟨SY, hSY⟩ := hD'fam.exists_finset
    obtain ⟨e, he, hecart⟩ := exists_zsmul_isCartier hYQ.2 SY
    refine ⟨e * bb, Nat.mul_pos he hbb, ?_⟩
    filter_upwards [hEev, hΓev, self_mem_nhdsWithin] with t ⟨hEt0, hEtsupp⟩ hΓt htW k hk C hC
      hCk F hF
    have htV : t ∈ V := hWV htW
    -- the push-forward `C'` of `C`, with `r C' = k (K_Y + Γ_t)`
    set C' : Divisor Y := RationalMap.transformDivisor φ C with hC'def
    have hC'k : Divisor.toRDivisor (((e * bb : ℕ) : ℤ) • C') =
        (k : ℝ) • (Divisor.toRDivisor KY + Γ t) := by
      rw [map_zsmul, hC'def, toRDivisor_transformDivisor, ← map_zsmul, ← map_zsmul, hCk,
        transformDivisor_smul, hD' t htV]
    have hC'supp : C'.support ⊆ SY :=
      support_subset_of_toRDivisor_zsmul_eq (Nat.mul_pos he hbb).ne' _ hC'k (hSY t)
    have hCe : ((e : ℤ) • C').IsCartier := hecart C' hC'supp
    obtain ⟨hDY, hfreeY⟩ :=
      isCartier_and_isRelativelyFreeDivisor_mul_zsmul hbb hk (hfree (Γ t) hΓt) hCe hC'k
    have hpos := pos_transformDivisor_of_pos_relativeFixedMultiplicity hX hY hT hZ p q fX fY hp
      hq hpX hqY hfX hfY hZc (hP t htV) (hQ t htV) (by rwa [hPV t htV, hQV t htV])
      (hqE t htV) (by exact_mod_cast hk) (hC.zsmul _) hCk hDY hC'k hfreeY hF
    obtain ⟨G', -, -, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX hTX hp F
    refine isInRelativeDivisorialStableBase_of_pos_transformDivisor hX hY hT p q fX fY hp hq hpX
      hqY hZc (hP δ hδV) (hQ δ hδV) (add_sub_cancel _ _).symm (hqE δ hδV) F ?_
    rw [DivisorWithCoeffs.coeff, htr, hPV δ hδV, hQV δ hδV]
    rw [DivisorWithCoeffs.coeff, htr, hPV t htV, hQV t htV] at hpos
    have hmem : G' ∈ (GP δ - GQ δ).support := hEtsupp ▸ Finsupp.mem_support_iff.2 hpos.ne'
    exact (hEδ' G').lt_of_ne (Finsupp.mem_support_iff.1 hmem).symm

end MMP.Fourfold
