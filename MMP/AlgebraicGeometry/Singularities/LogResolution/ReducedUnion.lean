module

public import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
public import MMP.AlgebraicGeometry.Divisor.OrderPullback
public import MMP.AlgebraicGeometry.Divisor.Principal
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentOrder

/-!
# Log resolutions and divisors supported on a log-resolved divisor (Lazarsfeld §9.1)

Let `g : Y' ⟶ Y` be a log resolution of an `ℝ`-divisor `S` on `Y`, and let `G₁, …, G_s` be
`ℝ`-divisors on `Y` with `Supp Gⱼ ⊆ Supp S`. Then `g^*G₁, …, g^*G_s` and `except(g)` have jointly
simple normal crossing support. Indeed, let `P` be a prime divisor of `Y'` occurring in some
`g^*Gⱼ`. If `P ⊆ Exc(g)`, it is a component of `except(g)`. Otherwise `g` is an open immersion
near the generic point `η` of `P`, so `g(η)` is the generic point of a prime divisor `Q` of `Y` and
`g^♯ : 𝒪_{Y,g(η)} → 𝒪_{Y',η}` is an isomorphism; orders along `P` of pull-backs are then orders
along `Q`, so `ord_P(g^*D) = ord_Q(D)` for every `ℝ`-divisor `D`. Hence `Q` is a component of `Gⱼ`,
so of `S`, and `P` is a component of `g^*S`. Every component of `[g^*G₁ ∪ ⋯ ∪ g^*G_s ∪ except(g)]`
is thus one of the SNC divisor `[g^*S ∪ except(g)]_red`, and sub-divisors of SNC divisors are SNC.

The order of an `ℝ`-divisor along a prime divisor `P` of a locally Noetherian scheme is the
`ℤ`-linear map `Div(X) ⊗ ℝ → ℝ` extending `ord_P`; it computes the coefficient of `P` in the Weil
divisor of `D` for *every* representation `D = ∑ cᵢ Aᵢ`.

## Main definitions

* `MMP.Intersection.primeDivisorOrder`: `ord_P : Div(X) → ℤ` along a prime divisor `P`.
* `MMP.Intersection.primeDivisorOrderR`: its `ℝ`-linear extension `Div(X) ⊗ ℝ → ℝ`.

## Main results

* `MMP.Intersection.IsWeilRDivisorOf.coeff_eq_primeDivisorOrderR`: the Weil divisor of an
  `ℝ`-divisor does not depend on the representation.
* `MMP.Intersection.IsWeilPullback.coeff_eq_of_genericPoint_eq`: along a prime divisor of `Y'`
  at whose generic point `g` is a local isomorphism, the coefficients of `g^*D` are those of `D`
  along the image prime divisor.
* `MMP.Intersection.IsLogResolution.hasJointSNCSupport_snoc`: the lemma above.

## Implementation notes

* The source's standing hypotheses that `Y` be a non-singular variety and `S` a reduced
  effective divisor are replaced by `Y` locally Noetherian and `S` an arbitrary `ℝ`-divisor,
  which is what the argument uses. `Y'` is locally Noetherian because it is a variety.
* `Supp Gⱼ ⊆ Supp S` is read on Weil divisors: `[Gⱼ]` and `[S]` are Weil `ℝ`-divisors of `Gⱼ`
  and `S` (`MMP.Intersection.IsWeilRDivisorOf`) and the inclusion is of their supports as closed
  subsets of `Y`.
* "`g^*G₁, …, g^*G_s` and `except(g)`" is the family `Fin.snoc F E` for any Weil divisors `Fⱼ`
  of pull-backs of the `Gⱼ` (`MMP.Intersection.IsWeilPullback`) and the exceptional divisor `E`.

## References

* R. Lazarsfeld, *Positivity in algebraic geometry*, II, §9.1
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry Order TensorProduct

namespace MMP.Intersection

open MMP.Mori (Divisor RDivisor DivisorWithCoeffs)

variable {X Y Y' : Scheme.{u}}

/-! ### The order along a prime divisor -/

section OrderAlongPrime

variable [IsLocallyNoetherian X]

/-- On a locally Noetherian scheme, every Cartier divisor has an order along every prime
divisor. -/
theorem exists_isOrderAlong_primeDivisor (D : X.CartierDivisor) (P : MMP.Mori.PrimeDivisor X) :
    ∃ N, IsOrderAlong D (primeDivisorSubvariety P) N := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk (primeDivisorSubvariety P).genericPoint) :=
    krullDimLE_of_coheight_le (by
      rw [show (primeDivisorSubvariety P).genericPoint = P.genericPoint from rfl,
        AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
      simp)
  exact exists_isOrderAlong D _

/-- The order `ord_P : Div(X) → ℤ` along a prime divisor `P` of a locally Noetherian scheme. -/
def primeDivisorOrder (P : MMP.Mori.PrimeDivisor X) : X.CartierDivisor →+ ℤ where
  toFun D := (exists_isOrderAlong_primeDivisor D P).choose
  map_zero' :=
    (exists_isOrderAlong_primeDivisor 0 P).choose_spec.unique (isOrderAlong_zero _)
  map_add' D₁ D₂ := (exists_isOrderAlong_primeDivisor (D₁ + D₂) P).choose_spec.unique
    ((exists_isOrderAlong_primeDivisor D₁ P).choose_spec.add
      (exists_isOrderAlong_primeDivisor D₂ P).choose_spec)

/-- `ord_P(D)` is an order of `D` along `P`. -/
theorem isOrderAlong_primeDivisorOrder (D : X.CartierDivisor) (P : MMP.Mori.PrimeDivisor X) :
    IsOrderAlong D (primeDivisorSubvariety P) (primeDivisorOrder P D) :=
  (exists_isOrderAlong_primeDivisor D P).choose_spec

/-- Any order `N` of `D` along `P` equals `ord_P(D)`. -/
theorem IsOrderAlong.primeDivisorOrder_eq {D : X.CartierDivisor} {P : MMP.Mori.PrimeDivisor X}
    {N : ℤ} (h : IsOrderAlong D (primeDivisorSubvariety P) N) : primeDivisorOrder P D = N :=
  (isOrderAlong_primeDivisorOrder D P).unique h

/-- The order `Div(X) ⊗ ℝ → ℝ` along a prime divisor `P`, the extension of `ord_P` by
`A ⊗ c ↦ c · ord_P(A)`. -/
def primeDivisorOrderR (P : MMP.Mori.PrimeDivisor X) : RCartierDivisor X →ₗ[ℤ] ℝ :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun (D : X.CartierDivisor) (r : ℝ) =>
      (primeDivisorOrder P D : ℝ) * r)
    (fun D₁ D₂ r => by rw [map_add, Int.cast_add, add_mul])
    (fun n D r => by rw [map_zsmul, zsmul_eq_mul, zsmul_eq_mul]; push_cast; ring)
    (fun D r₁ r₂ => mul_add _ _ _)
    (fun n D r => by rw [zsmul_eq_mul, zsmul_eq_mul]; ring))

/-- The order along `P` of `∑ Aᵢ ⊗ cᵢ` is `∑ cᵢ · ord_P(Aᵢ)`. -/
theorem primeDivisorOrderR_sum (P : MMP.Mori.PrimeDivisor X) {m : ℕ} (c : Fin m → ℝ)
    (A : Fin m → X.CartierDivisor) :
    primeDivisorOrderR P (∑ i, A i ⊗ₜ c i) = ∑ i, (primeDivisorOrder P (A i) : ℝ) * c i := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => TensorProduct.lift.tmul _ _

/-- **The Weil divisor of an `ℝ`-divisor is independent of the representation**: the coefficient
of `P` in any Weil divisor of `D` is `ord_P(D)`. -/
theorem IsWeilRDivisorOf.coeff_eq_primeDivisorOrderR {D : RCartierDivisor X} {w : RDivisor X}
    (h : IsWeilRDivisorOf D w) (P : MMP.Mori.PrimeDivisor X) :
    w.coeff P = primeDivisorOrderR P D := by
  obtain ⟨m, c, A, wA, hrep, hA, rfl⟩ := h
  rw [hrep, primeDivisorOrderR_sum]
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_smul,
    MMP.Mori.Divisor.coeff_toRDivisor, (hA i P).primeDivisorOrder_eq, smul_eq_mul, mul_comm]

/-- The Weil divisors of an `ℝ`-divisor are unique. -/
theorem IsWeilRDivisorOf.unique {D : RCartierDivisor X} {w w' : RDivisor X}
    (h : IsWeilRDivisorOf D w) (h' : IsWeilRDivisorOf D w') : w = w' :=
  MMP.Mori.DivisorWithCoeffs.ext' fun P =>
    (h.coeff_eq_primeDivisorOrderR P).trans (h'.coeff_eq_primeDivisorOrderR P).symm

end OrderAlongPrime

/-! ### Orders along a prime divisor where the morphism is a local isomorphism -/

/-- If `f^♯ : 𝒪_{Y,f(v')} → 𝒪_{Y',v'}` is an isomorphism at the generic point `v'` of `V'`, `f(v')`
is the generic point of `V`, and `A'` is a pull-back of `A`, then every order of `A` along `V` is
an order of `A'` along `V'`. -/
theorem IsPullback.isOrderAlong_of_isIso_stalkMap {f : Y' ⟶ Y} {A : Y.CartierDivisor}
    {A' : Y'.CartierDivisor} (h : IsPullback f A A') {V : Scheme.Subvariety Y}
    {V' : Scheme.Subvariety Y'} (hV : V.genericPoint = f V'.genericPoint)
    [IsIso (f.stalkMap V'.genericPoint)] [IsNoetherianRing (Y.presheaf.stalk (f V'.genericPoint))]
    [Ring.KrullDimLE 1 (Y.presheaf.stalk (f V'.genericPoint))] {N : ℤ}
    (hN : IsOrderAlong A V N) : IsOrderAlong A' V' N := by
  obtain ⟨a₀, b₀, ⟨g₀, hg₀, hab₀⟩, ha₀, hb₀, g₀', hg₀', hab₀'⟩ := h.2 V'.genericPoint
  let e := (asIso (f.stalkMap V'.genericPoint)).commRingCatIsoToRingEquiv
  have he : ∀ a, e a = f.stalkMap V'.genericPoint a := fun _ => rfl
  have hnzd : ∀ a, e a ∈ nonZeroDivisors _ →
      a ∈ nonZeroDivisors (Y.presheaf.stalk (f V'.genericPoint)) := by
    intro a ha
    rw [mem_nonZeroDivisors_iff] at ha ⊢
    exact ⟨fun x hx => (map_eq_zero_iff e e.injective).mp
        (ha.1 _ (by rw [← map_mul, hx, map_zero])),
      fun x hx => (map_eq_zero_iff e e.injective).mp (ha.2 _ (by rw [← map_mul, hx, map_zero]))⟩
  have ha₀' := hnzd _ ha₀
  have hb₀' := hnzd _ hb₀
  have h0 : IsOrderAlong A V ((Ring.ord _ a₀).toNat - (Ring.ord _ b₀).toNat) := by
    unfold IsOrderAlong
    rw [hV]
    exact ⟨a₀, b₀, ha₀', hb₀', ⟨g₀, hg₀, hab₀⟩, _, _,
      (ENat.natCast_toNat (Ring.ord_ne_top ha₀')).symm,
      (ENat.natCast_toNat (Ring.ord_ne_top hb₀')).symm, rfl⟩
  rw [hN.unique h0]
  refine ⟨_, _, ha₀, hb₀, ⟨g₀', hg₀', hab₀'⟩, _, _, ?_, ?_, rfl⟩
  · change Ring.ord _ _ = _
    rw [← he, ← Ring.ord_ringEquiv e a₀]
    exact (ENat.natCast_toNat (Ring.ord_ne_top ha₀')).symm
  · change Ring.ord _ _ = _
    rw [← he, ← Ring.ord_ringEquiv e b₀]
    exact (ENat.natCast_toNat (Ring.ord_ne_top hb₀')).symm

/-- A prime divisor whose generic point lies in another prime divisor is that prime divisor. -/
theorem primeDivisor_eq_of_genericPoint_mem_support {P Q : MMP.Mori.PrimeDivisor X}
    (h : Q.genericPoint ∈ P.support) : P = Q := by
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at h
  by_contra hne
  have hlt : (Q.genericPoint : X) < P.genericPoint :=
    lt_of_le_not_ge h (fun hge => hne (h.antisymm hge).eq)
  have := Order.coheight_strictAnti hlt
    (by simp [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint])
  simp [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at this

/-- A prime divisor not contained in the exceptional locus has its generic point outside it. -/
theorem genericPoint_notMem_exceptionalLocus {g : Y' ⟶ Y} {P : MMP.Mori.PrimeDivisor Y'}
    (hP : ¬ P.support ⊆ exceptionalLocus g) : P.genericPoint ∉ exceptionalLocus g := by
  refine fun hη => hP fun x hx => mem_exceptionalLocus_iff.mpr fun U hxU hU => ?_
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, mem_closure_iff] at hx
  obtain ⟨y, hyU, rfl⟩ := hx U U.isOpen hxU
  exact mem_exceptionalLocus_iff.mp hη U hyU hU

/-- If the prime divisor `P` of `Y'` is not contained in `Exc(g)`, then `g` maps its generic point
to the generic point of a prime divisor of `Y`, and `g^♯` is an isomorphism at it. -/
theorem exists_primeDivisor_genericPoint_eq_of_not_subset {g : Y' ⟶ Y}
    {P : MMP.Mori.PrimeDivisor Y'} (hP : ¬ P.support ⊆ exceptionalLocus g) :
    ∃ Q : MMP.Mori.PrimeDivisor Y, Q.genericPoint = g P.genericPoint ∧
      IsIso (g.stalkMap P.genericPoint) := by
  have hη := genericPoint_notMem_exceptionalLocus hP
  simp only [exceptionalLocus, Set.mem_ofPred_eq, not_not] at hη
  obtain ⟨U, hηU, hU⟩ := hη
  let x : U.toScheme := ⟨P.genericPoint, hηU⟩
  have hcoh : coheight (g P.genericPoint) = 1 := by
    have h1 := coheight_eq_of_isOpenImmersion (x := x) (U.ι ≫ g)
    have h2 := coheight_eq_of_isOpenImmersion (x := x) U.ι
    change coheight (g P.genericPoint) = _ at h1
    change coheight P.genericPoint = _ at h2
    rw [h1, ← h2]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _, ?_⟩
  have h3 : IsIso ((U.ι ≫ g).stalkMap x) := inferInstance
  rw [Scheme.Hom.stalkMap_comp] at h3
  have : IsIso (g.stalkMap (U.ι x)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ (U.ι.stalkMap x) inferInstance h3
  exact this

/-- **Coefficients of a pull-back away from the exceptional locus.** If `F` is a Weil divisor of a
pull-back of `D` along `g`, `w` a Weil divisor of `D`, and `g` maps the generic point of `P` to
that of `Q` with `g^♯` an isomorphism there, then `ord_P(F) = ord_Q(w)`. -/
theorem IsWeilPullback.coeff_eq_of_genericPoint_eq [IsLocallyNoetherian Y] [IsLocallyNoetherian Y']
    {g : Y' ⟶ Y} {D : RCartierDivisor Y} {F : RDivisor Y'} {w : RDivisor Y}
    (hF : IsWeilPullback g D F) (hw : IsWeilRDivisorOf D w) {P : MMP.Mori.PrimeDivisor Y'}
    {Q : MMP.Mori.PrimeDivisor Y} (hQ : Q.genericPoint = g P.genericPoint)
    [IsIso (g.stalkMap P.genericPoint)] : F.coeff P = w.coeff Q := by
  obtain ⟨m, c, A, D', ⟨hrep, -, A', hrep', hA'⟩, hD'⟩ := hF
  rw [hD'.coeff_eq_primeDivisorOrderR P, hw.coeff_eq_primeDivisorOrderR Q, hrep', hrep,
    primeDivisorOrderR_sum, primeDivisorOrderR_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : IsIso (g.stalkMap (primeDivisorSubvariety P).genericPoint) :=
    ‹IsIso (g.stalkMap P.genericPoint)›
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk (g (primeDivisorSubvariety P).genericPoint)) :=
    krullDimLE_of_coheight_le (by
      change coheight (g P.genericPoint) ≤ _
      rw [← hQ, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
      simp)
  rw [((hA' i).isOrderAlong_of_isIso_stalkMap (V := primeDivisorSubvariety Q)
    (V' := primeDivisorSubvariety P) hQ
    (isOrderAlong_primeDivisorOrder (A i) Q)).primeDivisorOrder_eq]

/-! ### Log resolutions of divisors supported on a log-resolved divisor -/

/-- **Log resolutions of a union of supports** (Lazarsfeld §9.1). Let `g : Y' ⟶ Y` be a log
resolution of the `ℝ`-divisor `S` on the locally Noetherian scheme `Y`, and `G₁, …, G_s`
`ℝ`-divisors on `Y` with `Supp Gⱼ ⊆ Supp S`. Then `g^*G₁, …, g^*G_s` and `except(g)` have jointly
simple normal crossing support. -/
@[mmp "lem_p09a_log_resolution_reduced_union"]
theorem IsLogResolution.hasJointSNCSupport_snoc [IsLocallyNoetherian Y] {k : Type u} [Field k]
    {sY : Y ⟶ Spec (.of k)} {S : RCartierDivisor Y} {wS : RDivisor Y} {g : Y' ⟶ Y}
    (hg : IsLogResolution sY S g) (hS : IsWeilRDivisorOf S wS) {s : ℕ}
    {G : Fin s → RCartierDivisor Y} {wG : Fin s → RDivisor Y}
    (hG : ∀ j, IsWeilRDivisorOf (G j) (wG j)) (hGS : ∀ j, (wG j).supp ≤ wS.supp)
    {F : Fin s → RDivisor Y'} (hF : ∀ j, IsWeilPullback g (G j) (F j)) {E : Divisor Y'}
    (hE : IsExceptionalDivisorSum g E) :
    HasJointSNCSupport (g ≫ sY)
      (Fin.snoc F (MMP.Mori.Divisor.toRDivisor E) : Fin (s + 1) → RDivisor Y') := by
  obtain ⟨-, -, hvar, -, FS, E₀, hFS, hE₀, hsnc⟩ := hg
  obtain rfl := hE₀.eq hE
  have : LocallyOfFiniteType (g ≫ sY) := hvar.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sY)
  refine IsSNCDivisor.of_support_subset hsnc (isReducedEffective_reducedDivisorOf _) ?_
  rw [reducedUnion, reducedUnion, support_reducedDivisorOf, support_reducedDivisorOf]
  intro P hP
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finsupp.mem_support_iff] at hP ⊢
  obtain ⟨j, hj⟩ := hP
  by_cases hPE : P.support ⊆ exceptionalLocus g
  · refine ⟨1, ?_⟩
    have := hE₀ P
    simp only [hPE, ↓reduceIte] at this
    change (MMP.Mori.Divisor.toRDivisor E₀) P ≠ 0
    rw [← DivisorWithCoeffs.coeff_apply, MMP.Mori.Divisor.coeff_toRDivisor, this]
    norm_num
  · refine ⟨0, ?_⟩
    obtain ⟨Q, hQ, hiso⟩ := exists_primeDivisor_genericPoint_eq_of_not_subset hPE
    have hQS : wS.coeff Q ≠ 0 := by
      induction j using Fin.lastCases with
      | last =>
        exfalso
        have := hE₀ P
        simp only [hPE, ↓reduceIte] at this
        rw [Fin.snoc_last, ← DivisorWithCoeffs.coeff_apply, MMP.Mori.Divisor.coeff_toRDivisor,
          this] at hj
        exact hj (by norm_num)
      | cast j =>
        rw [Fin.snoc_castSucc] at hj
        have hFj := (hF j).coeff_eq_of_genericPoint_eq (hG j) hQ
        rw [DivisorWithCoeffs.coeff_apply] at hFj
        have hmem : Q.genericPoint ∈ (wG j).supp :=
          DivisorWithCoeffs.mem_supp_iff.mpr ⟨Q, hFj ▸ hj,
            by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩
        obtain ⟨R, hR, hQR⟩ := DivisorWithCoeffs.mem_supp_iff.mp (hGS j hmem)
        rwa [← primeDivisor_eq_of_genericPoint_mem_support hQR]
    change FS P ≠ 0
    rwa [← DivisorWithCoeffs.coeff_apply, hFS.coeff_eq_of_genericPoint_eq hS hQ]

end MMP.Intersection
