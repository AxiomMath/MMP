module

public import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
public import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector

/-!
# The final model of the subtraction algorithm

Let `T` be a reduced snc divisor on a smooth variety `W`, `J` a set of components of `T`, `Z` an
irreducible component of `⋂_{j ∈ J} Tⱼ` and `α` a family of positive coprime weights on `J`. Over
an affine neighbourhood `U` of the generic point of `Z` meeting only the `Tⱼ`, the final model of
the subtraction algorithm is log crepant over `U` and carries a boundary component `E` whose
divisorial valuation is the monomial valuation of weight `α`, and which contains the centre of
every valuation of order vector `d • α` with centre `Z`.

## Main results

* `ModelCore.exists_model_core`: the last exceptional divisor carries the monomial valuation of
  weight `α`.
* `MMP.Mori.DivisorWithCoeffs.IsSNC.restrictOpen`: an snc divisor restricts to an snc divisor on
  every open subscheme.
* `MMP.Mori.inverseTransformDivisor_ι_eq_restrictOpen`: the inverse transform along the inclusion
  of an open subscheme is the restriction.
* `Restriction.exists_crepant_sncModel_monomialValuation`: the final model over `U`, its log
  crepancy over `U` and the centres of valuations of order vector `d • α`.
* `exists_isAffineOpen_nbhd`: an affine neighbourhood of the generic point of `Z` meeting only the
  components `Tⱼ`, `j ∈ J`, in which every intersection of some of the `Tⱼ` is preconnected.
-/

@[expose] public noncomputable section

universe uP

namespace MMP.Fourfold.SNCWeight

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing MvPolynomial
open scoped WithZero

namespace ModelCore

open MMP.Mori MMP.Resolution MMP.Threefold.Resolution PrimeDivisorUnion StratumBlowup SNCBlowup
  LocalEquation BlowupCrepancy SNCModel CentreLifting Subtraction

set_option linter.unusedSectionVars false

section Hartogs

variable {Z : Scheme.{uP}} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]

/-- The image in the function field of a germ at `y` has nonnegative order along every prime
divisor `Γ` through `y`. -/
theorem ord_algebraMap_nonneg (Γ : MMP.Mori.PrimeDivisor Z) {y : Z}
    (hy : y ∈ (Γ.support : Set Z)) (r : Z.presheaf.stalk y)
    (hr : algebraMap _ Z.functionField r ≠ 0) :
    0 ≤ Z.ord (algebraMap _ Z.functionField r) Γ.genericPoint := by
  have hsp := specializes_of_mem Γ hy
  have h1 : Γ.divisorialValuation (algebraMap _ Z.functionField r) ≤ 1 := by
    rw [Γ.divisorialValuation_le_one_iff, ← MMP.Mori.algebraMap_stalkSpecializes hsp]
    exact ⟨_, rfl⟩
  rw [Γ.divisorialValuation_eq_exp_neg_ord hr, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

/-- If `ξ` dominates `y` and `u` is a local equation at `y` of a prime divisor `H` through `y`,
then `ξ r ≤ ξ u ^ ord_H r` for every germ `r` at `y` with nonzero image in the function field. -/
theorem valuation_le_zpow_of_localEq {y : Z} {ξ : Valuation Z.functionField ℤᵐ⁰}
    (hξ : Dominates ξ y) (H : MMP.Mori.PrimeDivisor Z) (hyH : y ∈ (H.support : Set Z))
    {u : Z.presheaf.stalk y} (hu : IdealSheafData.stalk H.idealSheaf y = Ideal.span {u})
    (r : Z.presheaf.stalk y) (hr : algebraMap _ Z.functionField r ≠ 0) :
    ξ (algebraMap _ Z.functionField r) ≤
      ξ (algebraMap _ Z.functionField u) ^
        Z.ord (algebraMap _ Z.functionField r) H.genericPoint := by
  have hu0 := localEq_ne_zero H hyH hu
  have hg0 : algebraMap _ Z.functionField r * (algebraMap _ Z.functionField u) ^
      (-Z.ord (algebraMap _ Z.functionField r) H.genericPoint) ≠ 0 :=
    mul_ne_zero hr (zpow_ne_zero _ hu0)
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor Z, y ∈ Γ.support → 0 ≤ Z.ord
      (algebraMap _ Z.functionField r * (algebraMap _ Z.functionField u) ^
        (-Z.ord (algebraMap _ Z.functionField r) H.genericPoint)) Γ.genericPoint := by
    intro Γ hΓ
    rw [Scheme.ord_mul hr (zpow_ne_zero _ hu0), MMP.Mori.ord_zpow _ hu0,
      ord_localEq Γ H hΓ hyH hu]
    split_ifs with h
    · subst h
      omega
    · have := ord_algebraMap_nonneg Γ hΓ r hr
      omega
  obtain ⟨s, hs⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
    y hg0 hord
  have h1 : ξ (algebraMap _ Z.functionField r * (algebraMap _ Z.functionField u) ^
      (-Z.ord (algebraMap _ Z.functionField r) H.genericPoint)) ≤ 1 := hs ▸ hξ.1 s
  have hfg : algebraMap _ Z.functionField r = (algebraMap _ Z.functionField r *
      (algebraMap _ Z.functionField u) ^ (-Z.ord (algebraMap _ Z.functionField r) H.genericPoint)) *
      (algebraMap _ Z.functionField u) ^ Z.ord (algebraMap _ Z.functionField r) H.genericPoint := by
    rw [mul_assoc, ← zpow_add₀ hu0, neg_add_cancel, zpow_zero, mul_one]
  conv_lhs => rw [hfg]
  rw [map_mul, map_zpow₀]
  exact (mul_le_mul_left h1 _).trans_eq (one_mul _)

end Hartogs

section Extract

variable {k : Type uP} [Field k] [CharZero k] {X : Scheme.{uP}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX] {Δ : Divisor X}
  {n : ℕ} {η : X} {ι : Type*} [Fintype ι] [Nonempty ι] {z : ι → X.presheaf.stalk η}
  {α : ι → ℕ}

attribute [local instance] SModel.isIntegral SModel.isDominant SModel.isLocallyNoetherian
  SModel.isNormal

/-- For positive coprime weights `α`, a track with at most one divisor consists of a single
divisor `E`, with coefficient `1`, along which each `z j` has order `α j`. -/
theorem exists_single (hα : ∀ j, 0 < α j) (hαp : ∀ d : ℕ, (∀ j, d ∣ α j) → d = 1)
    (M : SModel sX Δ n) (t : M.Track η z α) (h1 : t.P.card ≤ 1) :
    ∃ E, t.P = {E} ∧ t.c E = 1 ∧ ∀ j, M.ordZ (z j) E = α j := by
  obtain ⟨j0⟩ := ‹Nonempty ι›
  have hne : t.P.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have := t.ray j0
    rw [he, Finset.sum_empty] at this
    have := hα j0
    omega
  obtain ⟨E, hE⟩ := Finset.card_eq_one.1 (le_antisymm h1 (Finset.card_pos.2 hne))
  have hray : ∀ j, (α j : ℤ) = t.c E * M.ordZ (z j) E := fun j => by
    rw [t.ray j, hE, Finset.sum_singleton]
  have hc1 : t.c E = 1 := hαp _ fun j => Int.natCast_dvd_natCast.1 ⟨_, hray j⟩
  exact ⟨E, hE, hc1, fun j => by simpa [hc1] using (hray j).symm⟩

/-- `WithZero.exp` of a finite sum is the product of the exponentials. -/
theorem exp_sum {G κ : Type*} [AddCommMonoid G] (s : Finset κ) (f : κ → G) :
    WithZero.exp (∑ i ∈ s, f i) = ∏ i ∈ s, WithZero.exp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [WithZero.exp_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, WithZero.exp_add, ih]

/-- A valuation on the stalk at `η` bounded by `1` and equal to `exp (-α j)` on each `z j` is at
most `exp (-N)` on the weighted monomial ideal of level `N`. -/
theorem weightedValuation_le (v : Valuation (X.presheaf.stalk η) ℤᵐ⁰)
    (hv1 : ∀ r, v r ≤ 1) {N : ℕ} (hvz : ∀ j, v (z j) = WithZero.exp (-(α j : ℤ)))
    {f : X.presheaf.stalk η} (hf : f ∈ MMP.Fourfold.weightedMonomialIdeal z α N) :
    v f ≤ WithZero.exp (-(N : ℤ)) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · rintro x ⟨β, hβ, rfl⟩
    rw [map_prod]
    have : ∏ i, v (z i ^ β i) = WithZero.exp (-((∑ i, α i * β i : ℕ) : ℤ)) := by
      rw [Nat.cast_sum, ← Finset.sum_neg_distrib, exp_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_pow, hvz, ← WithZero.exp_nsmul]
      congr 1
      push_cast
      ring
    rw [this, WithZero.exp_le_exp]
    omega
  · rw [map_zero]
    exact zero_le
  · intro x y _ _ hx hy
    exact (v.map_add x y).trans (max_le hx hy)
  · intro r x _ hx
    rw [smul_eq_mul, map_mul]
    exact ((mul_le_mul_left (hv1 r) _).trans_eq (one_mul _)).trans hx

/-- A function in the weighted monomial ideal of level `N` has valuation at most `exp (-N)` along
any prime divisor `E` through `p` on which each `z j` vanishes to order `α j`. -/
theorem divisorialValuation_stalkMap_le (M : SModel sX Δ n) {p : M.Y}
    {w : ι → X.presheaf.stalk (M.g p)} {E : MMP.Mori.PrimeDivisor M.Y}
    (hpE : p ∈ (E.support : Set M.Y)) (hord : ∀ j, M.ordZ (w j) E = α j)
    (hw : ∀ j, algebraMap _ X.functionField (w j) ≠ 0) {N : ℕ} {f : X.presheaf.stalk (M.g p)}
    (hf : f ∈ MMP.Fourfold.weightedMonomialIdeal w α N) :
    E.divisorialValuation (algebraMap _ M.Y.functionField ((M.g.stalkMap p).hom f)) ≤
      WithZero.exp (-(N : ℤ)) := by
  have hspE : E.genericPoint ⤳ p := specializes_of_mem E hpE
  let v : Valuation (X.presheaf.stalk (M.g p)) ℤᵐ⁰ := E.divisorialValuation.comap
    ((algebraMap (M.Y.presheaf.stalk p) M.Y.functionField).comp (M.g.stalkMap p).hom)
  have hv1 : ∀ r, v r ≤ 1 := by
    intro r
    simp only [v, Valuation.comap_apply, RingHom.coe_comp, Function.comp_apply]
    rw [E.divisorialValuation_le_one_iff, ← MMP.Mori.algebraMap_stalkSpecializes hspE]
    exact ⟨_, rfl⟩
  have hvz : ∀ j, v (w j) = WithZero.exp (-(α j : ℤ)) := by
    intro j
    simp only [v, Valuation.comap_apply, RingHom.coe_comp, Function.comp_apply]
    rw [← MMP.Mori.functionFieldMap_algebraMap_stalk,
      E.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr (hw j))]
    congr 2
    exact hord j
  simpa only [v, Valuation.comap_apply, RingHom.coe_comp, Function.comp_apply] using
    weightedValuation_le v hv1 hvz hf

/-- If a track consists of a single divisor `E` with coefficient `1` along which each `z j` has
order `α j`, then the divisorial valuation of `E` takes the value `exp (-N)` on a nonzero germ `f`
at `η`, where `N` is the largest level of a weighted monomial ideal containing `f`. -/
theorem monomial_of_final (hα : ∀ j, 0 < α j)
    (hspan : Ideal.span (Set.range z) = maximalIdeal (X.presheaf.stalk η))
    (hdim : ringKrullDim (X.presheaf.stalk η) = Fintype.card ι)
    (M : SModel sX Δ n) (t : M.Track η z α) {E : MMP.Mori.PrimeDivisor M.Y} (hE : t.P = {E})
    (hc1 : t.c E = 1) (hord : ∀ j, M.ordZ (z j) E = α j) (f : X.presheaf.stalk η) (hf : f ≠ 0) :
    ∃ N : ℕ, IsGreatest {m : ℕ | f ∈ MMP.Fourfold.weightedMonomialIdeal z α m} N ∧
      E.divisorialValuation (functionFieldMap M.g (algebraMap _ X.functionField f)) =
        WithZero.exp (-(N : ℤ)) := by
  obtain ⟨ν, hνf, hνz, hνle, hνlt⟩ :=
    WeightedOrder.exists_valuation_weightedOrder' z α (K := X.functionField) hα hspan hdim
  have hwv : IsWeightVal η z α ν 1 := ⟨one_pos, ⟨hνle, hνlt⟩, fun j => by simp [hνz]⟩
  let e := RingEquiv.ofBijective (functionFieldMap M.g) M.isBir.functionFieldMap_bijective
  let ξY : Valuation M.Y.functionField ℤᵐ⁰ := ν.comap e.symm.toRingHom
  have hcm : ξY.comap (functionFieldMap M.g) = ν := by
    ext x
    exact congrArg ν (e.symm_apply_apply x)
  haveI := M.isProper
  obtain ⟨p, hp, hgp⟩ := exists_dominates_of_isProper M.g ξY η (hcm ▸ hwv.2.1)
  obtain ⟨hpS, hpiff, hpval⟩ := t.cent ν 1 hwv ξY hcm p hp
  have hEP : E ∈ t.P := by simp [hE]
  have hEsupp := t.P_sub hEP
  have hpE : p ∈ (E.support : Set M.Y) := (hpiff E hEsupp).2 hEP
  obtain ⟨u, hu⟩ := exists_localEq_of_isSNC M.snc hEsupp hpE
  have hu1 : ξY (algebraMap _ _ u) = WithZero.exp (-1) := by
    simpa [hc1] using hpval E hEP u hu
  obtain ⟨N, hN, hνN⟩ := hνf f hf
  refine ⟨N, hN, ?_⟩
  subst hgp
  have hφ := MMP.Mori.functionFieldMap_algebraMap_stalk M.g p f
  have hf0 : algebraMap _ X.functionField f ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hf
  have hφ0 : algebraMap _ M.Y.functionField ((M.g.stalkMap p).hom f) ≠ 0 :=
    hφ ▸ (map_ne_zero _).mpr hf0
  have hle := valuation_le_zpow_of_localEq hp E hpE hu ((M.g.stalkMap p).hom f) hφ0
  have hξφ : ξY (algebraMap _ M.Y.functionField ((M.g.stalkMap p).hom f)) =
      WithZero.exp (-(N : ℤ)) := by
    rwa [← hφ, ← Valuation.comap_apply, hcm]
  rw [hξφ, hu1, ← WithZero.exp_zsmul, WithZero.exp_le_exp] at hle
  have hz0 : ∀ j, algebraMap _ X.functionField (z j) ≠ 0 := fun j h0 => by
    have := hνz j
    rw [h0, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  have hvf := divisorialValuation_stalkMap_le M hpE hord hz0 hN.1
  rw [E.divisorialValuation_eq_exp_neg_ord hφ0, WithZero.exp_le_exp] at hvf
  rw [hφ, E.divisorialValuation_eq_exp_neg_ord hφ0]
  congr 1
  simp only [smul_eq_mul] at hle
  omega

open Classical in
/-- On the base model, there is a track for `z` and `α` whose divisors are the components
of `Δ`. -/
theorem exists_base_track (B : BaseData sX Δ n η) (e : ι ≃ Δ.support)
    (hz : ∀ j, IdealSheafData.stalk (e j).1.idealSheaf η = Ideal.span {z j})
    (hα : ∀ j, 0 < α j) :
    ∃ t : (baseModel B).Track η z α, t.P = Δ.support := by
  haveI := B.isVariety
  refine ⟨{
    P := Δ.support
    c := fun P => if h : P ∈ Δ.support then α (e.symm ⟨P, h⟩) else 0
    S := {η}
    P_sub := subset_rfl
    c_pos := fun P hP => by simpa only [dif_pos hP] using hα _
    S_pre := isPreconnected_singleton
    S_ne := Set.singleton_nonempty η
    S_sub := fun P hP => Set.singleton_subset_iff.2 (B.mem P hP)
    S_over := fun y hy => hy
    ray := ?_
    cent := ?_ }, rfl⟩
  · intro j
    have key : ∀ P ∈ Δ.support, ((if h : P ∈ Δ.support then α (e.symm ⟨P, h⟩) else 0 : ℕ) : ℤ) *
        (baseModel B).ordZ (z j) P = if P = (e j).1 then (α j : ℤ) else 0 := by
      intro P hP
      change _ * X.ord (functionFieldMap (𝟙 X) (algebraMap _ X.functionField (z j)))
        P.genericPoint = _
      rw [MMP.Mori.functionFieldMap_id_apply,
        ord_localEq P (e j).1 (B.mem P hP) (B.mem _ (e j).2) (hz j), dif_pos hP]
      by_cases h : P = (e j).1
      · have h' : (⟨P, hP⟩ : Δ.support) = e j := Subtype.ext h
        rw [if_pos h, if_pos h, h', Equiv.symm_apply_apply]
        ring
      · rw [if_neg h, if_neg h]
        ring
    rw [Finset.sum_congr rfl key, Finset.sum_ite_eq', if_pos (e j).2]
  · intro ξ d hξ ξY hcm p hp
    have hξY : ξY = ξ := by
      rw [← hcm]
      ext f
      rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_id_apply]
    subst hξY
    have hpη : p = η := eq_of_dominates (sX := sX) hp hξ.2.1
    subst p
    refine ⟨rfl, fun F hF => ⟨fun _ => hF, fun _ => B.mem F hF⟩, fun F hF u hu => ?_⟩
    rw [dif_pos hF, ← hξ.2.2 (e.symm ⟨F, hF⟩)]
    refine valuation_eq_of_span_eq hξ.2.1 (hu.symm.trans ?_)
    rw [← hz, Equiv.apply_symm_apply]

/-- On a base whose boundary components all pass through `η`, with local equations `z` spanning
the maximal ideal at `η` and positive coprime weights `α`, there is a stratum tower model with a
boundary component `E` whose divisorial valuation is the monomial valuation of weight `α`, and
such that the centre of every valuation of weight `d • α` lies on `E` and on no other boundary
component. -/
theorem exists_model_core (B : BaseData sX Δ n η) (e : ι ≃ Δ.support)
    (hz : ∀ j, IdealSheafData.stalk (e j).1.idealSheaf η = Ideal.span {z j})
    (hα : ∀ j, 0 < α j) (hαp : ∀ d : ℕ, (∀ j, d ∣ α j) → d = 1)
    (hspan : Ideal.span (Set.range z) = maximalIdeal (X.presheaf.stalk η))
    (hdim : ringKrullDim (X.presheaf.stalk η) = Fintype.card ι)
    (hconn : StrataConnected Δ.support) :
    ∃ (M : SModel sX Δ n) (E : MMP.Mori.PrimeDivisor M.Y), M.IsStratumTower ∧ E ∈ M.T.support ∧
      (∀ f : X.presheaf.stalk η, f ≠ 0 →
        ∃ N : ℕ, IsGreatest {m : ℕ | f ∈ MMP.Fourfold.weightedMonomialIdeal z α m} N ∧
          E.divisorialValuation (functionFieldMap M.g (algebraMap _ X.functionField f)) =
            WithZero.exp (-(N : ℤ))) ∧
      ∀ (ξ : Valuation X.functionField ℤᵐ⁰) (d : ℕ), IsWeightVal η z α ξ d →
        ∀ ξY : Valuation M.Y.functionField ℤᵐ⁰, ξY.comap (functionFieldMap M.g) = ξ →
        ∀ p : M.Y, Dominates ξY p → p ∈ (E.support : Set M.Y) ∧
          ∀ F ∈ M.T.support, F ≠ E → p ∉ (F.support : Set M.Y) := by
  obtain ⟨t, htP⟩ := exists_base_track B e hz hα
  have hz' : ∀ j, ∃ P ∈ Δ.support, IdealSheafData.stalk P.idealSheaf η = Ideal.span {z j} :=
    fun j => ⟨_, (e j).2, hz j⟩
  obtain ⟨M, t, h1, htow⟩ := exists_final hz' (baseModel B) t (htP ▸ hconn)
    (baseModel_isStratumTower B)
  obtain ⟨E, hE, hc1, hord⟩ := exists_single hα hαp M t h1
  have hEP : E ∈ t.P := by simp [hE]
  refine ⟨M, E, htow, t.P_sub hEP, fun f hf => monomial_of_final hα hspan hdim M t hE hc1 hord f hf,
    fun ξ d hξ ξY hcm p hp => ?_⟩
  obtain ⟨-, hiff, -⟩ := t.cent ξ d hξ ξY hcm p hp
  refine ⟨(hiff E (t.P_sub hEP)).2 hEP, fun F hF hFE hpF => hFE ?_⟩
  simpa [hE] using (hiff F hF).1 hpF

end Extract

end ModelCore

namespace Restriction

open MMP.Mori MMP.Resolution MMP.Threefold.Resolution PrimeDivisorUnion StratumBlowup SNCBlowup
  LocalEquation BlowupCrepancy SNCModel CentreLifting Subtraction ModelCore

set_option linter.unusedSectionVars false

section Restrict

variable {W : Scheme.{uP}} (U : W.Opens)

/-- An open subscheme `U` lies in the biregular locus of its inclusion. -/
theorem le_biregularLocus_ι : U ≤ MMP.Mori.biregularLocus U.ι := by
  refine MMP.Mori.le_biregularLocus ?_
  change IsIso (U.ι ∣_ U)
  rw [isIso_iff_isOpenImmersion_and_epi_base]
  refine ⟨inferInstance, (TopCat.epi_iff_surjective _).mpr ?_⟩
  intro v
  have hv : v ∈ U.ι ⁻¹ᵁ U := by
    rw [Scheme.Opens.ι_preimage_self]
    trivial
  let p : (U.ι ⁻¹ᵁ U).toScheme := ⟨v, hv⟩
  refine ⟨p, U.ι.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  rfl

/-- The inclusion of an open subscheme `U` maps every point into `U`. -/
theorem ι_mem (u : U.toScheme) : U.ι u ∈ U := by
  have : U.ι u ∈ Set.range U.ι := ⟨u, rfl⟩
  rwa [Scheme.Opens.range_ι] at this

/-- The inverse transform of a prime divisor `Q` of `W` along `U.ι` is `P` exactly when `Q` is the
image of `P` in `W`. -/
theorem inverseTransformPrimeDivisor_ι_eq_some_iff (Q : MMP.Mori.PrimeDivisor W)
    (P : MMP.Mori.PrimeDivisor U.toScheme) :
    inverseTransformPrimeDivisor U.ι Q = some P ↔
      Q = OpenWeilRestriction.primeDivisorMap U.ι P := by
  constructor
  · intro h
    obtain ⟨h1, -⟩ := map_genericPoint_of_inverseTransformPrimeDivisor_eq_some h
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (h1.symm.trans (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P).symm)
  · rintro rfl
    exact inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P).symm
      (le_biregularLocus_ι U (ι_mem U _))

/-- The inverse transform of a divisor under the inclusion of an open subscheme `U` is its
restriction to `U`. -/
theorem _root_.MMP.Mori.inverseTransformDivisor_ι_eq_restrictOpen {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R W) :
    inverseTransformDivisor U.ι D = D.restrictOpen U := by
  ext P
  change DivisorWithCoeffs.mapPrimeDivisors _ D P = _
  rw [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((inverseTransformPrimeDivisor_ι_eq_some_iff U _ P).2 rfl)
    (fun E' h => (inverseTransformPrimeDivisor_ι_eq_some_iff U E' P).1 h)]
  rfl

/-- The stalk at `u` of the ideal sheaf of a prime divisor `P` of `U` is the extension, along the
stalk map of `U.ι`, of the stalk at `U.ι u` of the ideal sheaf of the image of `P` in `W`. -/
theorem stalk_primeDivisorMap_comap (P : MMP.Mori.PrimeDivisor U.toScheme) (u : U.toScheme) :
    IdealSheafData.stalk P.idealSheaf u = Ideal.map (U.ι.stalkMap u).hom
      (IdealSheafData.stalk (OpenWeilRestriction.primeDivisorMap U.ι P).idealSheaf (U.ι u)) := by
  rw [← MMP.Threefold.Mori.OpenRestriction.stalk_comap_eq_map,
    MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap]

/-- A prime divisor of `U` is a component of `T|_U` exactly when its image in `W` is a component
of `T`. -/
theorem mem_support_restrictOpen_iff (T : Divisor W) (P : MMP.Mori.PrimeDivisor U.toScheme) :
    P ∈ (T.restrictOpen U).support ↔ OpenWeilRestriction.primeDivisorMap U.ι P ∈ T.support := by
  rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]
  rfl

/-- If every component of `T` meeting `U` lies in `J`, then a prime divisor of `U` whose image in
`W` is a component of `T` has image in `J`. -/
theorem primeDivisorMap_mem_of_mem {T : Divisor W} {J : Finset (MMP.Mori.PrimeDivisor W)}
    (hU : ∀ E ∈ T.support, (E.support ∩ U).Nonempty → E ∈ J) (P : MMP.Mori.PrimeDivisor U.toScheme)
    (hP : OpenWeilRestriction.primeDivisorMap U.ι P ∈ T.support) :
    OpenWeilRestriction.primeDivisorMap U.ι P ∈ J := by
  refine hU _ hP ⟨U.ι P.genericPoint, ?_, ι_mem U _⟩
  rw [← OpenWeilRestriction.genericPoint_primeDivisorMap,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- The restriction of an snc divisor on a scheme locally of finite type over a field to an
open subscheme is snc. -/
theorem _root_.MMP.Mori.DivisorWithCoeffs.IsSNC.restrictOpen {R : Type*} [Zero R]
    {k : Type uP} [Field k] {sW : W ⟶ Spec (.of k)} [LocallyOfFiniteType sW]
    {D : DivisorWithCoeffs R W} (hD : D.IsSNC sW) : (D.restrictOpen U).IsSNC (U.ι ≫ sW) := by
  refine ⟨fun E hE => ?_, fun x =>
    (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U.ι D x).mpr (hD.2 (U.ι x))⟩
  have hsm := hD.1 (OpenWeilRestriction.primeDivisorMap U.ι E)
    (Finsupp.mem_support_iff.2 (Finsupp.mem_support_iff.1 hE : D.restrictOpen U E ≠ 0))
  have : LocallyOfFinitePresentation
      ((OpenWeilRestriction.primeDivisorMap U.ι E).idealSheaf.subschemeι ≫ sW) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  rw [IsSmoothScheme, MMP.Mori.smoothLocus_eq_smoothLocus] at hsm
  exact (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff U.ι sW
    (OpenWeilRestriction.primeDivisorMap U.ι E).idealSheaf E.idealSheaf
    (MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap U.ι E)).mpr
    fun z _ => hsm ▸ trivial

end Restrict

/-- Two families generating the same principal ideals termwise span the same ideal. -/
theorem span_range_eq_span_image_of_span_singleton_eq {R J N : Type*} [CommSemiring R]
    [Fintype J] [DecidableEq N] {z : J → R} {w : N → R} {f : J → N}
    (h : ∀ j, Ideal.span {z j} = Ideal.span {w (f j)}) :
    Ideal.span (Set.range z) = Ideal.span (w '' ((Finset.univ.image f : Finset N) : Set N)) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : z j ∈ Ideal.span {w (f j)} := by
      rw [← h j]
      exact Ideal.subset_span rfl
    have h2 : w (f j) ∈ w '' ((Finset.univ.image f : Finset N) : Set N) := ⟨f j, by simp, rfl⟩
    exact Ideal.span_mono (Set.singleton_subset_iff.2 h2) h1
  · rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi
    have h1 : w (f j) ∈ Ideal.span {z j} := by
      rw [h j]
      exact Ideal.subset_span rfl
    have h2 : z j ∈ Set.range z := ⟨j, rfl⟩
    exact Ideal.span_mono (Set.singleton_subset_iff.2 h2) h1

/-- A Noetherian local ring whose maximal ideal is spanned by a finite family has Krull dimension
at most the size of the family. -/
theorem ringKrullDim_le_card_of_span_range_eq {R J : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Fintype J] {z : J → R}
    (h : Ideal.span (Set.range z) = maximalIdeal R) : ringKrullDim R ≤ Fintype.card J := by
  have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.finite_range z)
  change (Ideal.span (Set.range z)).spanFinrank ≤ _ at h1
  rw [h] at h1
  have h2 : (Set.range z).ncard ≤ Fintype.card J := by
    rw [← Set.image_univ]
    refine (Set.ncard_image_le Set.finite_univ).trans ?_
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  calc ringKrullDim R
      ≤ ((maximalIdeal R).spanFinrank : WithBot ℕ∞) := ringKrullDim_le_spanFinrank_maximalIdeal _
    _ ≤ (Fintype.card J : WithBot ℕ∞) := by exact_mod_cast h1.trans h2

/-- A ring isomorphism of local rings carries a family spanning the maximal ideal to a family
spanning the maximal ideal. -/
theorem span_range_map_eq_maximalIdeal {R S J : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (φ : R ≃+* S) {z : J → R}
    (h : Ideal.span (Set.range z) = maximalIdeal R) :
    Ideal.span (Set.range fun j => φ (z j)) = maximalIdeal S := by
  have e := Ideal.map_span φ (Set.range z)
  rw [← Set.range_comp, h] at e
  rw [show Ideal.span (Set.range fun j => φ (z j)) = _ from e.symm]
  exact IsLocalRing.map_ringEquiv_maximalIdeal φ

section Setup

variable {k : Type uP} [Field k] {W : Scheme.{uP}} {sW : W ⟶ Spec (.of k)} [IsIntegral W]
  [IsLocallyNoetherian W] {T : Divisor W} {J : Finset (MMP.Mori.PrimeDivisor W)}
  {Z : IrreducibleCloseds W}
  (hZ : Maximal (fun S : Set W => IsIrreducible S ∧ S ⊆ ⋂ E ∈ J, E.support) (Z : Set W))
  {U : W.Opens} (hηU : Z.isIrreducible.genericPoint ∈ U)
  (hU : ∀ E ∈ T.support, (E.support ∩ U).Nonempty → E ∈ J)

include hZ in
/-- The generic point of `Z` lies on every member of `J`. -/
theorem genericPoint_mem_support_of_mem {j : MMP.Mori.PrimeDivisor W} (hj : j ∈ J) :
    Z.isIrreducible.genericPoint ∈ (j.support : Set W) :=
  Set.mem_iInter₂.1 (hZ.1.2
    (Z.isClosed.closure_subset Z.isIrreducible.isGenericPoint_genericPoint_closure.mem)) j hj

include hZ hU in
/-- The generic point of `Z` lies on every component of `T|_U`. -/
theorem mem_restrict_of_mem_support (P : MMP.Mori.PrimeDivisor U.toScheme)
    (hP : P ∈ (T.restrictOpen U).support) :
    (⟨Z.isIrreducible.genericPoint, hηU⟩ : U.toScheme) ∈ (P.support : Set U.toScheme) := by
  rw [mem_support_restrictOpen_iff] at hP
  have hJ := primeDivisorMap_mem_of_mem U hU P hP
  have := genericPoint_mem_support_of_mem hZ hJ
  exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι P _).1 this

include hZ hηU in
/-- Every member of `J` is the image in `W` of a prime divisor of `U`. -/
theorem exists_restrict (j : J) :
    ∃ P : MMP.Mori.PrimeDivisor U.toScheme, OpenWeilRestriction.primeDivisorMap U.ι P = j.1 :=
  MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support U.ι j.1
    (⟨Z.isIrreducible.genericPoint, hηU⟩ : U.toScheme) (genericPoint_mem_support_of_mem hZ j.2)

include hZ hηU hU in
/-- The components of `J` restricted to `U`, as the components of `T|_U`. -/
def restrictEquiv (hJT : J ⊆ T.support) : J ≃ (T.restrictOpen U).support :=
  Equiv.ofBijective
    (fun j => ⟨(exists_restrict hZ hηU j).choose, by
      rw [mem_support_restrictOpen_iff, (exists_restrict hZ hηU j).choose_spec]
      exact hJT j.2⟩)
    ⟨fun a b hab => Subtype.ext (by
      have h := congrArg (fun P : (T.restrictOpen U).support =>
        OpenWeilRestriction.primeDivisorMap U.ι P.1) hab
      simp only at h
      rwa [(exists_restrict hZ hηU a).choose_spec, (exists_restrict hZ hηU b).choose_spec] at h),
     fun P => by
      have hP := (mem_support_restrictOpen_iff U T P.1).1 P.2
      exact ⟨⟨_, primeDivisorMap_mem_of_mem U hU P.1 hP⟩, Subtype.ext <|
        OpenWeilRestriction.primeDivisorMap_injective U.ι
          (exists_restrict hZ hηU ⟨_, primeDivisorMap_mem_of_mem U hU P.1 hP⟩).choose_spec⟩⟩

/-- The image in `W` of the component `restrictEquiv hZ hηU hU hJT j` of `T|_U` is `j`. -/
@[simp]
theorem primeDivisorMap_restrictEquiv (hJT : J ⊆ T.support) (j : J) :
    OpenWeilRestriction.primeDivisorMap U.ι (restrictEquiv hZ hηU hU hJT j).1 = j.1 :=
  (exists_restrict hZ hηU j).choose_spec

/-- A local equation `z` of `j` at the generic point of `Z` gives, through the stalk isomorphism of
`U ⊆ W`, a local equation there of the component `restrictEquiv hZ hηU hU hJT j` of `T|_U`. -/
theorem stalk_restrictEquiv (hJT : J ⊆ T.support) (j : J)
    {z : W.presheaf.stalk Z.isIrreducible.genericPoint}
    (hz : IdealSheafData.stalk j.1.idealSheaf Z.isIrreducible.genericPoint = Ideal.span {z}) :
    IdealSheafData.stalk (restrictEquiv hZ hηU hU hJT j).1.idealSheaf (⟨_, hηU⟩ : U.toScheme) =
      Ideal.span {(MMP.Threefold.Mori.OpenRestriction.stalkEquivOfOpenImmersion U.ι
        (⟨_, hηU⟩ : U.toScheme) z)} := by
  let u : U.toScheme := ⟨_, hηU⟩
  change IdealSheafData.stalk _ u = Ideal.span
    {MMP.Threefold.Mori.OpenRestriction.stalkEquivOfOpenImmersion U.ι u z}
  rw [stalk_primeDivisorMap_comap, primeDivisorMap_restrictEquiv]
  change Ideal.map _ (IdealSheafData.stalk j.1.idealSheaf Z.isIrreducible.genericPoint) = _
  rw [hz]
  have e1 := Ideal.map_span (U.ι.stalkMap u).hom {z}
  rw [Set.image_singleton] at e1
  exact e1

include hZ hηU hU in
/-- For a reduced snc divisor `T` on a smooth variety `W`, the open subscheme `U`, the divisor
`T|_U` and the generic point of `Z` form base data of some dimension `n`. -/
theorem exists_baseData (hW : MMP.Mori.IsVariety k sW) (hWs : IsSmoothScheme sW)
    (hT : MMP.Intersection.IsReducedEffective T) (hTs : T.IsSNC sW) :
    haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
    ∃ n : ℕ, Nonempty (BaseData (U.ι ≫ sW) (T.restrictOpen U) n ⟨_, hηU⟩) := by
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI : AlgebraicGeometry.IsVariety k sW := hW
  haveI hUv : AlgebraicGeometry.IsVariety k (U.ι ≫ sW) := by
    haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
    haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
    haveI : IsNoetherian W := ⟨⟩
    exact { }
  haveI : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ sW)
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k (U.ι ≫ sW)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim U = n := by
    induction hd : topologicalKrullDim U using WithBot.recBotCoe with
    | bot =>
      exact ((Order.krullDim_eq_bot_iff.mp hd).false
        (IrreducibleCloseds.closureSingleton (genericPoint U))).elim
    | coe d =>
      lift d to ℕ using fun h => h1 (by rw [hd, h]; rfl)
      exact ⟨d, rfl⟩
  haveI : Smooth sW := smooth_of_isSmoothScheme hWs
  refine ⟨n, ⟨{
    isVariety := hUv
    isSmooth := isSmoothScheme_of_smooth _
    dim := hn
    red := fun _ => hT _
    snc := hTs.restrictOpen U
    mem := fun P hP => mem_restrict_of_mem_support hZ hηU hU P hP }⟩⟩

include hZ in
/-- For an snc divisor `T` and `Z = closure {η}`, local equations `z` at `η` of the members of `J`
span the maximal ideal of the local ring at `η`, whose Krull dimension is the cardinality
of `J`. -/
theorem span_range_eq_and_ringKrullDim (hTs : T.IsSNC sW)
    (hJT : J ⊆ T.support) {η : W} (hZcl : (Z : Set W) = closure {η})
    (hmem : ∀ j : J, η ∈ (j.1.support : Set W)) (z : J → W.presheaf.stalk η)
    (hz : ∀ j : J, IdealSheafData.stalk j.1.idealSheaf η = Ideal.span {z j}) :
    Ideal.span (Set.range z) = maximalIdeal (W.presheaf.stalk η) ∧
      ringKrullDim (W.presheaf.stalk η) = Fintype.card J := by
  classical
  obtain ⟨N, w, jj, hw, hjj, hI⟩ := hTs.2 η
  let ι' : J → {E : MMP.Mori.PrimeDivisor W // E ∈ T.support ∧ η ∈ E.support} :=
    fun j => ⟨j.1, hJT j.2, hmem j⟩
  have hι' : Function.Injective ι' := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  let Jset : Finset (Fin N) := Finset.univ.image (fun j => jj (ι' j))
  have hzw : ∀ j : J, Ideal.span {z j} = Ideal.span {w (jj (ι' j))} := fun j => by
    rw [← hz j, ← hI (ι' j)]
  have hspan : Ideal.span (Set.range z) = Ideal.span (w '' (Jset : Set (Fin N))) :=
    span_range_eq_span_image_of_span_singleton_eq (f := fun j => jj (ι' j)) hzw
  have hprime : (Ideal.span (Set.range z)).IsPrime := by
    rw [hspan]
    exact span_image_isPrime_of_isRegularSystemOfParameters hw Jset
  let P : PrimeSpectrum (W.presheaf.stalk η) := ⟨_, hprime⟩
  have hyJ : ∀ j : J, W.fromSpecStalk η P ∈ (j.1.support : Set W) := fun j =>
    (fromSpecStalk_mem_support_iff_stalk_le _ η P).2 <| by
      rw [hz j]
      exact Ideal.span_mono (Set.singleton_subset_iff.2 ⟨j, rfl⟩)
  have hcl : closure {W.fromSpecStalk η P} ⊆ ⋂ E ∈ J, (E.support : Set W) := by
    refine Set.subset_iInter₂ fun E hE => closure_minimal
      (Set.singleton_subset_iff.2 (hyJ ⟨E, hE⟩)) ?_
    exact (E.idealSheaf.support).isClosed
  have hZy : (Z : Set W) ⊆ closure {W.fromSpecStalk η P} := by
    rw [hZcl]
    exact closure_minimal (Set.singleton_subset_iff.2
      (specializes_iff_mem_closure.1 (fromSpecStalk_specializes_self η P))) isClosed_closure
  have hyZ := hZ.2 ⟨isIrreducible_singleton.closure, hcl⟩ hZy
  have hy1 : W.fromSpecStalk η P ⤳ η := fromSpecStalk_specializes_self η P
  have hy2 : η ⤳ W.fromSpecStalk η P := by
    rw [specializes_iff_mem_closure, ← hZcl]
    exact hyZ (subset_closure rfl)
  have hyη : W.fromSpecStalk η P = η := (hy1.antisymm hy2).eq
  have hmax : maximalIdeal (W.presheaf.stalk η) ≤ P.asIdeal :=
    (fromSpecStalk_mem_closure_iff η (IsLocalRing.closedPoint _) P).1 (by
      rw [hyη, Scheme.fromSpecStalk_closedPoint]
      exact subset_closure rfl)
  have hspan' : Ideal.span (Set.range z) = maximalIdeal (W.presheaf.stalk η) :=
    le_antisymm (IsLocalRing.le_maximalIdeal hprime.ne_top) hmax
  refine ⟨hspan', le_antisymm (ringKrullDim_le_card_of_span_range_eq hspan') ?_⟩
  rw [hw.2]
  have := Fintype.card_le_of_injective _ (hjj.comp hι')
  rw [Fintype.card_fin] at this
  exact_mod_cast this

include hZ hηU hU in
/-- The union of the components of `T|_U` is the preimage in `U` of the union of the members
of `J`. -/
theorem iUnion_support_restrictOpen (hJT : J ⊆ T.support) :
    (⋃ P ∈ (T.restrictOpen U).support, (P.support : Set U.toScheme)) =
      U.ι ⁻¹' ⋃ E ∈ J, (E.support : Set W) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]
  constructor
  · rintro ⟨P, hP, hxP⟩
    have hP' := (mem_support_restrictOpen_iff U T P).1 hP
    exact ⟨_, primeDivisorMap_mem_of_mem U hU P hP',
      (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι P x).2 hxP⟩
  · rintro ⟨E, hE, hxE⟩
    refine ⟨(restrictEquiv hZ hηU hU hJT ⟨E, hE⟩).1, (restrictEquiv hZ hηU hU hJT ⟨E, hE⟩).2, ?_⟩
    rwa [← MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι,
      primeDivisorMap_restrictEquiv]

include hU in
/-- The strata of `T|_U` are preconnected when the intersections of the `Tⱼ`, `j ∈ J`, meet `U`
in preconnected sets. -/
theorem strataConnected_restrictOpen
    (hUc : ∀ K ⊆ J, _root_.IsPreconnected ((⋂ E ∈ K, (E.support : Set W)) ∩ U)) :
    StrataConnected (T.restrictOpen U).support := by
  classical
  intro K hK
  set K0 := K.image (OpenWeilRestriction.primeDivisorMap U.ι) with hK0
  have hK0J : K0 ⊆ J := by
    intro E hE
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hE
    exact primeDivisorMap_mem_of_mem U hU P ((mem_support_restrictOpen_iff U T P).1 (hK hP))
  have heq : (⋂ P ∈ K, (P.support : Set U.toScheme)) = U.ι ⁻¹' ⋂ E ∈ K0, (E.support : Set W) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_preimage, hK0, Finset.mem_image, forall_exists_index,
      and_imp]
    constructor
    · rintro h E P hP rfl
      exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι P x).2 (h P hP)
    · intro h P hP
      exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι P x).1
        (h _ P hP rfl)
  rw [heq, ← U.ι.isOpenEmbedding.isInducing.isPreconnected_image, Set.image_preimage_eq_inter_range,
    Scheme.Opens.range_ι]
  exact hUc K0 hK0J

omit [IsIntegral W] [IsLocallyNoetherian W] in
/-- For an snc divisor `T`, the members of `J ⊆ T.support` passing through `η` have local
equations at `η`. -/
theorem exists_localEqs (hTs : T.IsSNC sW) (hJT : J ⊆ T.support) {η : W}
    (hmem : ∀ j : J, η ∈ (j.1.support : Set W)) :
    ∃ z0 : J → W.presheaf.stalk η,
      ∀ j : J, IdealSheafData.stalk j.1.idealSheaf η = Ideal.span {z0 j} := by
  obtain ⟨N, w, jj, -, -, hI⟩ := hTs.2 η
  exact ⟨fun j => w (jj ⟨j.1, hJT j.2, hmem j⟩), fun j => hI ⟨j.1, hJT j.2, hmem j⟩⟩

end Setup

section Crep

variable {k : Type uP} [Field k] [CharZero k] {X : Scheme.{uP}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX] {Δ : Divisor X}
  {n : ℕ} {η : X}

attribute [local instance] SModel.isIntegral SModel.isDominant SModel.isLocallyNoetherian
  SModel.isNormal

/-- For every model `M` over the base `B`, there is a canonical divisor `K` of `X` for which
`M.T` is a crepant boundary of `(X, Δ)` along `M.g`. -/
theorem exists_isCrepantBoundary (B : BaseData sX Δ n η) (M : SModel sX Δ n) :
    ∃ K : Divisor X, K.IsCanonicalDivisor sX n ∧
      IsCrepantBoundary sX n K (Divisor.toQDivisor Δ) M.g ⟨M.isVariety, SModel.isNormal M⟩
        M.isBir (Divisor.toQDivisor M.T) := by
  haveI := B.isVariety
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sX B.isSmooth B.dim
  have hXnv : IsNormalVariety k sX := ⟨B.isVariety, inferInstance⟩
  have hCart :
      (((1 : ℕ) : ℤ) • (Divisor.toQDivisor K + Divisor.toQDivisor Δ)).IsCartierDivisor := by
    rw [Nat.cast_one, one_smul, ← map_add, QDivisor.isCartierDivisor_toQDivisor]
    exact MMP.Fourfold.isCartier_of_isSmoothScheme B.isSmooth _
  have hpair : MMP.Mori.IsPair sX (Divisor.toQDivisor Δ) :=
    ⟨hXnv, n, K, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme B.isSmooth _⟩
  refine ⟨K, hK, fun F => ?_⟩
  obtain ⟨-, U0, hU0, τ, hgen⟩ := MMP.Positivity.IsPair.exists_generatesOn hpair hK hCart
    (M.g F.genericPoint)
  refine ⟨hXnv, hK, 1, one_pos, hCart, U0, hU0, τ, hgen, ?_⟩
  have := M.crep F U0 τ hU0 hgen
  change (((1 : ℕ) : ℚ)) * (-(Divisor.toQDivisor M.T).coeff F) =
    ((F.ordForm (pullbackRationalPluriForms sX M.g τ) : ℤ) : ℚ)
  rw [this, Divisor.coeff_toQDivisor]
  push_cast
  ring

end Crep

section WeightedMap

/-- A ring isomorphism `φ` carries the weighted monomial ideal of `z` to that of `φ ∘ z`. -/
theorem map_weightedMonomialIdeal {A B : Type*} [CommRing A] [CommRing B] {ι : Type*}
    [Fintype ι] (φ : A ≃+* B) (z : ι → A) (α : ι → ℕ) (m : ℕ) :
    Ideal.map φ (MMP.Fourfold.weightedMonomialIdeal z α m) =
      MMP.Fourfold.weightedMonomialIdeal (fun i => φ (z i)) α m := by
  rw [MMP.Fourfold.weightedMonomialIdeal, MMP.Fourfold.weightedMonomialIdeal, Ideal.map_span]
  congr 1
  ext r
  constructor
  · rintro ⟨_, ⟨β, hβ, rfl⟩, rfl⟩
    exact ⟨β, hβ, by simp [map_prod]⟩
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨_, ⟨β, hβ, rfl⟩, by simp [map_prod]⟩

/-- For a ring isomorphism `φ`, `φ f` lies in the weighted monomial ideal of `φ ∘ z` exactly when
`f` lies in that of `z`. -/
theorem mem_weightedMonomialIdeal_map_iff {A B : Type*} [CommRing A] [CommRing B] {ι : Type*}
    [Fintype ι] (φ : A ≃+* B) (z : ι → A) (α : ι → ℕ) (m : ℕ) (f : A) :
    φ f ∈ MMP.Fourfold.weightedMonomialIdeal (fun i => φ (z i)) α m ↔
      f ∈ MMP.Fourfold.weightedMonomialIdeal z α m := by
  rw [← map_weightedMonomialIdeal]
  exact Ideal.apply_mem_of_equiv_iff

/-- For positive weights, the ideal spanned by the `z i` lies in the weighted ideal of
level `1`. -/
theorem span_range_le_weightedMonomialIdeal_one {A : Type*} [CommRing A] {ι : Type*}
    [Fintype ι] (z : ι → A) {α : ι → ℕ} (hα : ∀ i, 0 < α i) :
    Ideal.span (Set.range z) ≤ MMP.Fourfold.weightedMonomialIdeal z α 1 := by
  classical
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  apply Ideal.subset_span
  refine ⟨Pi.single i 1, ?_, ?_⟩
  · rw [Finset.sum_eq_single i (fun b _ hb => by simp [Pi.single_apply, hb])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp only [Pi.single_eq_same, mul_one]
    exact hα i
  · rw [Finset.prod_eq_single i (fun b _ hb => by simp [Pi.single_apply, hb])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp

end WeightedMap

section Centres

variable {k : Type uP} [Field k]

/-- Restricting along a bijective ring map `f` the transport of `v` along `f⁻¹` gives back `v`. -/
theorem comap_comap_ofBijective_symm {K L Γ : Type*} [Ring K] [Ring L]
    [LinearOrderedCommMonoidWithZero Γ] (f : K →+* L) (hf : Function.Bijective f)
    (v : Valuation K Γ) :
    (v.comap (RingEquiv.ofBijective f hf).symm.toRingHom).comap f = v := by
  ext x
  exact congrArg v ((RingEquiv.ofBijective f hf).symm_apply_apply x)

/-- Transporting along `f⁻¹` the restriction of `v` along a bijective ring map `f` gives back
`v`. -/
theorem comap_ofBijective_symm_comap {K L Γ : Type*} [Ring K] [Ring L]
    [LinearOrderedCommMonoidWithZero Γ] (f : K →+* L) (hf : Function.Bijective f)
    (v : Valuation L Γ) :
    (v.comap f).comap (RingEquiv.ofBijective f hf).symm.toRingHom = v := by
  ext x
  exact congrArg v ((RingEquiv.ofBijective f hf).apply_symm_apply x)

/-- A valuation computing the weighted order of every nonzero germ at `η`, for weights `α > 0`
and a system of generators `z` of the maximal ideal, dominates `η`. -/
theorem dominates_of_weightedOrder {X : Scheme.{uP}} [IsIntegral X] {η : X} {ι : Type*}
    [Fintype ι] {z : ι → X.presheaf.stalk η} {α : ι → ℕ} (hα : ∀ i, 0 < α i)
    (hspan : Ideal.span (Set.range z) = maximalIdeal (X.presheaf.stalk η))
    {v : Valuation X.functionField ℤᵐ⁰}
    (hv : ∀ f : X.presheaf.stalk η, f ≠ 0 →
      ∃ N : ℕ, IsGreatest {m : ℕ | f ∈ MMP.Fourfold.weightedMonomialIdeal z α m} N ∧
        v (algebraMap _ X.functionField f) = WithZero.exp (-(N : ℤ))) :
    Dominates v η := by
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · by_cases ha0 : a = 0
    · rw [ha0, map_zero, map_zero]
      exact zero_le
    · obtain ⟨N, -, hN⟩ := hv a ha0
      rw [hN, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
  · by_cases ha0 : a = 0
    · rw [ha0, map_zero, map_zero]
      exact zero_lt_one
    · obtain ⟨N, hNg, hN⟩ := hv a ha0
      have := hNg.2 (span_range_le_weightedMonomialIdeal_one z hα (by rwa [hspan]))
      rw [hN, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega

/-- The valuation of a divisor over `X` dominates the image in `X` of the generic point of the
divisor. -/
theorem dominates_divisorOver {X : Scheme.{uP}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    (D : MMP.Mori.DivisorOver k sX) : Dominates D.valuation (D.f D.E.genericPoint) := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · change D.E.divisorialValuation (functionFieldMap D.f (algebraMap _ X.functionField a)) ≤ 1
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk, D.E.divisorialValuation_le_one_iff]
    exact ⟨_, rfl⟩
  · change D.E.divisorialValuation (functionFieldMap D.f (algebraMap _ X.functionField a)) < 1
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact (D.E.divisorialValuation_algebraMap_lt_one_iff _).2
      ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu))

/-- A valuation with centre `Z = closure {η}` is the valuation of a proper divisor over `X` whose
generic point maps to `η`. -/
theorem exists_eq_of_isCentre {X : Scheme.{uP}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    {v : Valuation X.functionField ℤᵐ⁰} {Z : IrreducibleCloseds X} {η : X}
    (hZ : (Z : Set X) = closure {η}) (h : MMP.Intersection.IsCentre k sX v Z) :
    ∃ D : MMP.Mori.DivisorOver k sX, IsProper D.f ∧ v = D.valuation ∧ D.f D.E.genericPoint = η := by
  obtain ⟨D, hD, rfl, hZD⟩ := h
  refine ⟨D, hD, rfl, ?_⟩
  have h1 : closure {D.f D.E.genericPoint} = closure ({η} : Set X) := by
    rw [← D.center_eq_closure_genericPoint, ← hZD, hZ]
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- A valuation with centre `Z = closure {η}` dominates `η`. -/
theorem dominates_of_isCentre {X : Scheme.{uP}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    {v : Valuation X.functionField ℤᵐ⁰} {Z : IrreducibleCloseds X} {η : X}
    (hZ : (Z : Set X) = closure {η}) (h : MMP.Intersection.IsCentre k sX v Z) :
    Dominates v η := by
  obtain ⟨D, -, rfl, hD⟩ := exists_eq_of_isCentre hZ h
  rw [← hD]
  exact dominates_divisorOver D

/-- A divisorial valuation of the function field of a variety `X` dominating `x` has centre
`closure {x}`. -/
theorem isCentre_of_dominates {X : Scheme.{uP}} (sX : X ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sX] [IsIntegral X] {v : Valuation X.functionField ℤᵐ⁰}
    (hv : MMP.Flips.IsDivisorOfFunctionField k sX v) (x : X) (hx : Dominates v x) :
    MMP.Intersection.IsCentre k sX v (IrreducibleCloseds.closureSingleton x) := by
  obtain ⟨D'', -, hv'', hx''⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sX hv x hx.1 hx.2
  refine ⟨D''.toDivisorOver, D''.isProper, hv''.symm, ?_⟩
  ext1
  rw [D''.toDivisorOver.center_eq_closure_genericPoint]
  change closure {x} = closure {D''.f D''.E.genericPoint}
  rw [hx'']

/-- For a normal variety `Y` with a dominant morphism `h : Y ⟶ X` inducing an isomorphism of
function fields, the divisorial valuation of a prime divisor of `Y` is a divisorial valuation of
the function field of `X`. -/
theorem isDivisorOfFunctionField_comap_primeDivisor {X Y : Scheme.{uP}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] (h : Y ⟶ X) (hY : IsNormalVariety k (h ≫ sX))
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsDominant h]
    (hbij : Function.Bijective (functionFieldMap h)) (E : MMP.Mori.PrimeDivisor Y) :
    MMP.Flips.IsDivisorOfFunctionField k sX (E.divisorialValuation.comap (functionFieldMap h)) :=
  ⟨Y, h ≫ sX, hY, E, MMP.Mori.functionFieldAlgEquiv sX h hbij, by ext x; rfl⟩

/-- For a dominant morphism `h : Y ⟶ X` inducing an isomorphism of function fields, the valuation
of a divisor over `X`, transported to the function field of `Y`, is a divisorial valuation of the
function field of `Y`. -/
theorem isDivisorOfFunctionField_transport {X Y : Scheme.{uP}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral Y] (h : Y ⟶ X) [IsDominant h]
    (hbij : Function.Bijective (functionFieldMap h)) (D : MMP.Mori.DivisorOver k sX) :
    MMP.Flips.IsDivisorOfFunctionField k (h ≫ sX)
      (D.valuation.comap (RingEquiv.ofBijective (functionFieldMap h) hbij).symm.toRingHom) := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hbijD : Function.Bijective (functionFieldMap D.f) :=
    D.isBirationalMorphism.functionFieldMap_bijective
  letI := MMP.Mori.functionFieldAlgebra sX
  letI := MMP.Mori.functionFieldAlgebra (h ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
  refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E,
    (MMP.Mori.functionFieldAlgEquiv sX h hbij).symm.trans
      (MMP.Mori.functionFieldAlgEquiv sX D.f hbijD), ?_⟩
  ext x
  change D.E.divisorialValuation (functionFieldMap D.f
    ((RingEquiv.ofBijective (functionFieldMap h) hbij).symm x)) =
    D.E.divisorialValuation (functionFieldMap D.f
      ((MMP.Mori.functionFieldAlgEquiv sX h hbij).symm x))
  congr 2

/-- If `h : Y ⟶ X` induces an isomorphism of function fields and `ξ'` restricts along `h` to a
valuation with centre `Z = closure {η}`, then `ξ'` has centre `closure {p}` at every point `p` it
dominates. -/
theorem isCentre_closureSingleton_of_comap {X Y : Scheme.{uP}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral Y] (h : Y ⟶ X) [IsDominant h]
    [AlgebraicGeometry.IsVariety k (h ≫ sX)] (hbij : Function.Bijective (functionFieldMap h))
    {Z : IrreducibleCloseds X} {η : X} (hZ : (Z : Set X) = closure {η})
    {ξ : Valuation X.functionField ℤᵐ⁰} (hcent : MMP.Intersection.IsCentre k sX ξ Z)
    {ξ' : Valuation Y.functionField ℤᵐ⁰} (hcm : ξ'.comap (functionFieldMap h) = ξ) {p : Y}
    (hp : Dominates ξ' p) :
    MMP.Intersection.IsCentre k (h ≫ sX) ξ' (IrreducibleCloseds.closureSingleton p) := by
  obtain ⟨D, -, rfl, -⟩ := exists_eq_of_isCentre hZ hcent
  have hξ' : ξ' = D.valuation.comap
      (RingEquiv.ofBijective (functionFieldMap h) hbij).symm.toRingHom := by
    rw [← hcm]
    exact (comap_ofBijective_symm_comap _ hbij ξ').symm
  subst hξ'
  exact isCentre_of_dominates _ (isDivisorOfFunctionField_transport sX h hbij D) p hp

end Centres

section Transport

variable {W : Scheme.{uP}} [IsIntegral W] (U : W.Opens) [Nonempty U] [IsDominant U.ι]
  (u : U.toScheme) {ι : Type*} {z z0 : ι → W.presheaf.stalk (U.ι u)}
  (hzz : ∀ j, Ideal.span {z j} = Ideal.span {z0 j}) {α : ι → ℕ}

include hzz in
/-- A valuation of weight `d • α` on the local equations `z` at the image of `u ∈ U` dominating
it, transported to the function field of `U`, has weight `d • α` on the images in `U` of the
equations `z0`. -/
theorem isWeightVal_comap_restrict (hbijU : Function.Bijective (functionFieldMap U.ι))
    {ξ : Valuation W.functionField ℤᵐ⁰} (hdom : Dominates ξ (U.ι u)) {d : ℕ} (hd : 0 < d)
    (hval : ∀ j, ξ (algebraMap _ W.functionField (z j)) = WithZero.exp (-((d * α j : ℕ) : ℤ))) :
    IsWeightVal u
      (fun j => MMP.Threefold.Mori.OpenRestriction.stalkEquivOfOpenImmersion U.ι u (z0 j)) α
      (ξ.comap (RingEquiv.ofBijective (functionFieldMap U.ι) hbijU).symm.toRingHom) d := by
  set φ := MMP.Threefold.Mori.OpenRestriction.stalkEquivOfOpenImmersion U.ι u
  have hst : ∀ f : W.presheaf.stalk (U.ι u),
      functionFieldMap U.ι (algebraMap _ W.functionField f) =
        algebraMap _ U.toScheme.functionField (φ f) := fun f =>
    MMP.Mori.functionFieldMap_algebraMap_stalk U.ι u f
  have hξU : ∀ x, (ξ.comap (RingEquiv.ofBijective _ hbijU).symm.toRingHom)
      (functionFieldMap U.ι x) = ξ x := fun x =>
    congrArg ξ ((RingEquiv.ofBijective _ hbijU).symm_apply_apply x)
  refine ⟨hd, ⟨fun a => ?_, fun a ha => ?_⟩, fun j => ?_⟩
  · obtain ⟨b, rfl⟩ := φ.surjective a
    rw [← hst, hξU]
    exact hdom.1 b
  · obtain ⟨b, rfl⟩ := φ.surjective a
    rw [← hst, hξU]
    exact hdom.2 b ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (hu.map φ))
  · change (ξ.comap _) (algebraMap _ _ (φ (z0 j))) = _
    rw [← hst, hξU, ← valuation_eq_of_span_eq hdom (hzz j)]
    exact hval j

include hzz in
/-- If a function `v` on the function field of `U` computes the weighted order of every nonzero
germ at `u ∈ U` with respect to the images of `z0`, then any `v'` restricting along `U ⊆ W` to
`v` computes the weighted order of every nonzero germ at the image of `u` with respect to `z`. -/
theorem exists_isGreatest_of_restrict [Fintype ι] {v : U.toScheme.functionField → ℤᵐ⁰}
    {v' : W.functionField → ℤᵐ⁰} (hvv : ∀ x, v' x = v (functionFieldMap U.ι x))
    (hv : ∀ f : U.toScheme.presheaf.stalk u, f ≠ 0 →
      ∃ N : ℕ, IsGreatest {m : ℕ | f ∈ MMP.Fourfold.weightedMonomialIdeal
        (fun j => MMP.Threefold.Mori.OpenRestriction.stalkEquivOfOpenImmersion U.ι u (z0 j)) α m}
        N ∧
        v (algebraMap _ U.toScheme.functionField f) = WithZero.exp (-(N : ℤ)))
    (f : W.presheaf.stalk (U.ι u)) (hf : f ≠ 0) :
    ∃ N : ℕ, IsGreatest {m : ℕ | f ∈ MMP.Fourfold.weightedMonomialIdeal z α m} N ∧
      v' (algebraMap _ W.functionField f) = WithZero.exp (-(N : ℤ)) := by
  set φ := MMP.Threefold.Mori.OpenRestriction.stalkEquivOfOpenImmersion U.ι u
  obtain ⟨N, hN, hval⟩ := hv (φ f) fun h0 => hf (φ.injective (h0.trans (map_zero φ).symm))
  have hst : functionFieldMap U.ι (algebraMap _ W.functionField f) =
      algebraMap _ U.toScheme.functionField (φ f) :=
    MMP.Mori.functionFieldMap_algebraMap_stalk U.ι u f
  refine ⟨N, ?_, by rwa [hvv, hst]⟩
  have hset : {m : ℕ | f ∈ MMP.Fourfold.weightedMonomialIdeal z α m} =
      {m : ℕ | φ f ∈ MMP.Fourfold.weightedMonomialIdeal (fun j => φ (z0 j)) α m} := by
    ext m
    simp only [Set.mem_setOf_eq]
    rw [MMP.Fourfold.weightedMonomialIdeal_eq_of_span_eq hzz]
    exact (mem_weightedMonomialIdeal_map_iff φ z0 α m f).symm
  rwa [hset]

end Transport

section Final

variable {k : Type uP} [Field k] {W : Scheme.{uP}} (sW : W ⟶ Spec (.of k))
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

attribute [local instance] SModel.isIntegral SModel.isDominant SModel.isLocallyNoetherian
  SModel.isNormal

/-- A composite of dominant morphisms of integral schemes inducing isomorphisms of function fields
induces an isomorphism of function fields. -/
theorem bijective_functionFieldMap_comp {A B C : Scheme.{uP}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b]
    (ha : Function.Bijective (functionFieldMap a)) (hb : Function.Bijective (functionFieldMap b)) :
    Function.Bijective (functionFieldMap (a ≫ b)) := by
  rw [show ⇑(functionFieldMap (a ≫ b)) = functionFieldMap a ∘ functionFieldMap b from
    funext fun t => (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply a b t).symm]
  exact ha.comp hb

/-- Let `T` be an snc divisor, `Z = closure {u}` for a point `u` of an open `U` lying on every
member of `J`, and `h : Y ⟶ U` birational. If the divisorial valuation of a prime divisor `E` of
`Y` computes the weighted order at `u`, then its restriction to `W` has centre `Z` and computes the
weighted order with respect to any local equations `z` at `u`. -/
theorem isCentre_and_weightedOrder_of_restrict [AlgebraicGeometry.IsVariety k sW] {T : Divisor W}
    (hTs : T.IsSNC sW) {J : Finset (MMP.Mori.PrimeDivisor W)} (hJT : J ⊆ T.support)
    {Z : IrreducibleCloseds W}
    (hZ : Maximal (fun S : Set W => IsIrreducible S ∧ S ⊆ ⋂ E ∈ J, E.support) (Z : Set W))
    {U : W.Opens} [Nonempty U] [IsDominant U.ι] {u : U.toScheme}
    (hZcl : (Z : Set W) = closure {U.ι u}) (hmem : ∀ j : J, U.ι u ∈ (j.1.support : Set W))
    {α : J → ℕ} (hα : ∀ j, 0 < α j) {z0 z : J → W.presheaf.stalk (U.ι u)}
    (hz0 : ∀ j : J, IdealSheafData.stalk j.1.idealSheaf (U.ι u) = Ideal.span {z0 j})
    (hz : ∀ j : J, IdealSheafData.stalk j.1.idealSheaf (U.ι u) = Ideal.span {z j})
    {Y : Scheme.{uP}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (h : Y ⟶ U)
    [IsDominant h] (hY : IsNormalVariety k ((h ≫ U.ι) ≫ sW))
    (hbij : Function.Bijective (functionFieldMap (h ≫ U.ι))) (E : MMP.Mori.PrimeDivisor Y)
    (hmono : ∀ f : U.toScheme.presheaf.stalk u, f ≠ 0 →
      ∃ N : ℕ, IsGreatest {m : ℕ | f ∈ MMP.Fourfold.weightedMonomialIdeal
        (fun j => MMP.Threefold.Mori.OpenRestriction.stalkEquivOfOpenImmersion U.ι u (z0 j)) α m}
        N ∧
        E.divisorialValuation (functionFieldMap h (algebraMap _ U.toScheme.functionField f)) =
          WithZero.exp (-(N : ℤ))) :
    MMP.Intersection.IsCentre k sW (E.divisorialValuation.comap (functionFieldMap (h ≫ U.ι))) Z ∧
      ∀ f : W.presheaf.stalk (U.ι u), f ≠ 0 →
        ∃ N : ℕ, IsGreatest {m : ℕ | f ∈ MMP.Fourfold.weightedMonomialIdeal z α m} N ∧
          E.divisorialValuation.comap (functionFieldMap (h ≫ U.ι))
            (algebraMap _ W.functionField f) = WithZero.exp (-(N : ℤ)) := by
  have hform := exists_isGreatest_of_restrict U u (z := z) (z0 := z0)
    (fun i => (hz i).symm.trans (hz0 i))
    (v := fun y => E.divisorialValuation (functionFieldMap h y))
    (v' := E.divisorialValuation.comap (functionFieldMap (h ≫ U.ι)))
    (fun x => congrArg E.divisorialValuation
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply h U.ι x).symm) hmono
  have hdom := dominates_of_weightedOrder hα
    (span_range_eq_and_ringKrullDim hZ hTs hJT hZcl hmem z hz).1 hform
  have hcentre := isCentre_of_dominates sW
    (isDivisorOfFunctionField_comap_primeDivisor sW (h ≫ U.ι) hY hbij E) _ hdom
  have hZeq : IrreducibleCloseds.closureSingleton (U.ι u) = Z := by
    ext1
    exact hZcl.symm
  exact ⟨hZeq ▸ hcentre, hform⟩

/-- Let `Z = closure {u}` for a point `u` of an open `U`, and `h : Y ⟶ U` proper birational. If
for every valuation of weight `d • α` at `u` all the points it dominates on `Y` satisfy `P`, then
every valuation of `W` of order vector `d • α` with centre `Z` lifts to a valuation of `Y` with
centre the closure of a point satisfying `P`. -/
theorem exists_isCentre_of_restrict {J : Finset (MMP.Mori.PrimeDivisor W)}
    {Z : IrreducibleCloseds W} {U : W.Opens} [Nonempty U] [IsDominant U.ι] {u : U.toScheme}
    (hZcl : (Z : Set W) = closure {U.ι u}) {α : J → ℕ} {z0 z : J → W.presheaf.stalk (U.ι u)}
    (hz0 : ∀ j : J, IdealSheafData.stalk j.1.idealSheaf (U.ι u) = Ideal.span {z0 j})
    (hz : ∀ j : J, IdealSheafData.stalk j.1.idealSheaf (U.ι u) = Ideal.span {z j})
    {Y : Scheme.{uP}} [IsIntegral Y] (h : Y ⟶ U) [IsDominant h] [IsProper h]
    [AlgebraicGeometry.IsVariety k ((h ≫ U.ι) ≫ sW)]
    (hbijU : Function.Bijective (functionFieldMap U.ι))
    (hbijh : Function.Bijective (functionFieldMap h)) {P : Y → Prop}
    (hP : ∀ (ξ : Valuation U.toScheme.functionField ℤᵐ⁰) (d : ℕ),
      IsWeightVal u
        (fun j => MMP.Threefold.Mori.OpenRestriction.stalkEquivOfOpenImmersion U.ι u (z0 j)) α ξ d →
      ∀ ξY : Valuation Y.functionField ℤᵐ⁰, ξY.comap (functionFieldMap h) = ξ →
      ∀ p : Y, SNCModel.Dominates ξY p → P p)
    {ξ : Valuation W.functionField ℤᵐ⁰} (hcent : MMP.Intersection.IsCentre k sW ξ Z) {d : ℕ}
    (hd : 0 < d)
    (hval : ∀ j, ξ (algebraMap _ W.functionField (z j)) = WithZero.exp (-((d * α j : ℕ) : ℤ))) :
    ∃ (ξ' : Valuation Y.functionField ℤᵐ⁰) (p : Y),
      ξ'.comap (functionFieldMap (h ≫ U.ι)) = ξ ∧
      MMP.Intersection.IsCentre k ((h ≫ U.ι) ≫ sW) ξ' (IrreducibleCloseds.closureSingleton p) ∧
      P p := by
  have hcompff : ∀ x, functionFieldMap (h ≫ U.ι) x =
      functionFieldMap h (functionFieldMap U.ι x) := fun x =>
    (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply h U.ι x).symm
  have hbij := bijective_functionFieldMap_comp h U.ι hbijh hbijU
  have hwv := isWeightVal_comap_restrict U u (z := z) (z0 := z0)
    (fun j => (hz j).symm.trans (hz0 j)) hbijU (dominates_of_isCentre hZcl hcent) hd hval
  let ξU := ξ.comap (RingEquiv.ofBijective _ hbijU).symm.toRingHom
  let ξ' := ξU.comap (RingEquiv.ofBijective _ hbijh).symm.toRingHom
  have hcmh : ξ'.comap (functionFieldMap h) = ξU := comap_comap_ofBijective_symm _ hbijh ξU
  have hcm : ξ'.comap (functionFieldMap (h ≫ U.ι)) = ξ := by
    ext x
    rw [Valuation.comap_apply, hcompff, ← Valuation.comap_apply, hcmh]
    exact congrArg ξ ((RingEquiv.ofBijective _ hbijU).symm_apply_apply x)
  obtain ⟨p, hp, -⟩ := exists_dominates_of_isProper h ξ' u (hcmh ▸ hwv.2.1)
  exact ⟨ξ', p, hcm, isCentre_closureSingleton_of_comap sW (h ≫ U.ι) hbij hZcl hcent hcm hp,
    hP ξU d hwv ξ' hcmh p hp⟩

/-- Let `T` be a reduced snc divisor on a smooth variety `W`, `Z` an irreducible component of
`⋂_{j ∈ J} Tⱼ`, `U` an affine neighbourhood of the generic point of `Z` meeting only the `Tⱼ` and
in which every intersection of some of the `Tⱼ` is preconnected, and `α` positive coprime weights.
Then there is a projective birational boundary stratum blowup sequence `g : W' ⟶ U` with `W'`
smooth and a reduced snc divisor `T'` on `W'`, supported on the preimage of `⋃_{j ∈ J} Tⱼ` and
containing the exceptional set, which is crepant over `(U, T|_U)`; and a component `E` of `T'`
whose divisorial valuation is the monomial valuation of weight `α`, such that every valuation of
order vector `d • α` with centre `Z` has, on `W'`, a centre contained in `E` and in no other
component of `T'`. -/
theorem exists_crepant_sncModel_monomialValuation [CharZero k]
    (hW : MMP.Mori.IsVariety k sW) (hWs : IsSmoothScheme sW) (T : Divisor W)
    (hT : MMP.Intersection.IsReducedEffective T) (hTs : T.IsSNC sW)
    (J : Finset (MMP.Mori.PrimeDivisor W)) (hJ : J.Nonempty) (hJT : J ⊆ T.support)
    (Z : IrreducibleCloseds W)
    (hZ : Maximal (fun S : Set W => IsIrreducible S ∧ S ⊆ ⋂ E ∈ J, E.support) (Z : Set W))
    (U : W.Opens) (hηU : Z.isIrreducible.genericPoint ∈ U)
    (hU : ∀ E ∈ T.support, (E.support ∩ U).Nonempty → E ∈ J) (hUa : IsAffineOpen U)
    (hUc : ∀ K ⊆ J, _root_.IsPreconnected ((⋂ E ∈ K, (E.support : Set W)) ∩ U))
    (α : J → ℕ) (hα : ∀ j, 0 < α j) (hαp : ∀ d : ℕ, (∀ j, d ∣ α j) → d = 1) :
    haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
    ∃ (W' : Scheme.{uP}) (_ : IsIntegral W') (_ : IsLocallyNoetherian W') (_ : IsNormal W')
      (g : W' ⟶ U) (hg : IsBirationalMorphism g) (_ : IsDominant (g ≫ U.ι))
      (hW' : IsNormalVariety k (g ≫ U.ι ≫ sW)) (T' : Divisor W'),
      IsProjectiveMorphism g ∧
      (∃ (B : MMP.Resolution.ClosedBlowupSequence U) (h : W' = B.target),
        eqToHom h ≫ B.toBase = g ∧
        BlowupTower.IsBoundaryStratumSequence (U.ι.base ⁻¹' ⋃ E ∈ J, (E.support : Set W))
          (𝟙 U.toScheme) B) ∧
      IsSmoothScheme (g ≫ U.ι ≫ sW) ∧
      MMP.Intersection.IsReducedEffective T' ∧ T'.IsSNC (g ≫ U.ι ≫ sW) ∧
      (⋃ F ∈ T'.support, (F.support : Set W')) =
        (g ≫ U.ι).base ⁻¹' (⋃ E ∈ J, (E.support : Set W)) ∧
      (exceptionalSet g : Set W') ⊆ ⋃ F ∈ T'.support, (F.support : Set W') ∧
      (∃ (n : ℕ) (K : Divisor U), K.IsCanonicalDivisor (U.ι ≫ sW) n ∧
        IsCrepantBoundary (U.ι ≫ sW) n K
          (Divisor.toQDivisor (inverseTransformDivisor U.ι T)) g hW' hg
          (Divisor.toQDivisor T')) ∧
      ∃ E ∈ T'.support,
        (∀ z : J → W.presheaf.stalk Z.isIrreducible.genericPoint,
          (∀ j : J, IdealSheafData.stalk j.1.idealSheaf Z.isIrreducible.genericPoint =
            Ideal.span {z j}) →
          MMP.Fourfold.IsMonomialValuationOfWeight sW T J Z z α
            (E.divisorialValuation.comap (functionFieldMap (g ≫ U.ι)))) ∧
        ∀ (ξ : Valuation W.functionField ℤᵐ⁰) (d : ℕ)
          (z : J → W.presheaf.stalk Z.isIrreducible.genericPoint),
          (∀ j : J, IdealSheafData.stalk j.1.idealSheaf Z.isIrreducible.genericPoint =
            Ideal.span {z j}) →
          MMP.Intersection.IsCentre k sW ξ Z → 0 < d →
          (∀ j, ξ (algebraMap _ W.functionField (z j)) = WithZero.exp (-((d * α j : ℕ) : ℤ))) →
          ∃ (ξ' : Valuation W'.functionField ℤᵐ⁰) (C' : IrreducibleCloseds W'),
            ξ'.comap (functionFieldMap (g ≫ U.ι)) = ξ ∧
            MMP.Intersection.IsCentre k (g ≫ U.ι ≫ sW) ξ' C' ∧
            (C' : Set W') ⊆ E.support ∧
            ∀ F ∈ T'.support, F ≠ E → ¬ (C' : Set W') ⊆ F.support := by
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  classical
  haveI : AlgebraicGeometry.IsVariety k sW := hW
  haveI : LocallyOfFiniteType sW := hW.toLocallyOfFiniteType
  have hmem : ∀ j : J, Z.isIrreducible.genericPoint ∈ (j.1.support : Set W) := fun j =>
    genericPoint_mem_support_of_mem hZ j.2
  obtain ⟨z0, hz0⟩ := exists_localEqs hTs hJT hmem
  have hZcl : (Z : Set W) = closure {Z.isIrreducible.genericPoint} :=
    (Z.isClosed.closure_eq ▸ Z.isIrreducible.isGenericPoint_genericPoint_closure).symm
  obtain ⟨hspanW, hdimW⟩ := span_range_eq_and_ringKrullDim hZ hTs hJT hZcl hmem z0 hz0
  obtain ⟨n, ⟨B⟩⟩ := exists_baseData hZ hηU hU hW hWs hT hTs
  let ηU : U.toScheme := ⟨_, hηU⟩
  let φ : W.presheaf.stalk Z.isIrreducible.genericPoint ≃+* U.toScheme.presheaf.stalk ηU :=
    MMP.Threefold.Mori.OpenRestriction.stalkEquivOfOpenImmersion U.ι ηU
  haveI : Nonempty J := hJ.coe_sort
  obtain ⟨M, E, htow, hE, hmono, hcentM⟩ := exists_model_core B (restrictEquiv hZ hηU hU hJT)
    (z := fun j => φ (z0 j)) (fun j => stalk_restrictEquiv hZ hηU hU hJT j (hz0 j)) hα hαp
    (span_range_map_eq_maximalIdeal φ hspanW) ((ringKrullDim_eq_of_ringEquiv φ).symm.trans hdimW)
    (strataConnected_restrictOpen hU hUc)
  haveI : IsDominant U.ι := AlgebraicGeometry.Opens.isDominant_ι (U.isOpen.dense ⟨_, hηU⟩)
  have hbijU : Function.Bijective (functionFieldMap U.ι) :=
    MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤ ⟨ηU, trivial⟩
  have hbijM : Function.Bijective (functionFieldMap M.g) := M.isBir.functionFieldMap_bijective
  have hW' : IsNormalVariety k (M.g ≫ U.ι ≫ sW) := ⟨M.isVariety, inferInstance⟩
  obtain ⟨K, hK, hcrep⟩ := exists_isCrepantBoundary B M
  refine ⟨M.Y, inferInstance, inferInstance, inferInstance, M.g, M.isBir, inferInstance, hW', M.T,
    ?_, ?_, M.isSmooth, M.red, M.snc, ?_, M.exc, ⟨n, K, hK, ?_⟩, E, hE, ?_, ?_⟩
  · haveI : IsAffine U := hUa
    exact isProjectiveMorphism_of_isProjective_of_isAffine M.g M.isProj
  · obtain ⟨Bt, h, hg, hBt⟩ := htow
    exact ⟨Bt, h, hg, by rwa [← iUnion_support_restrictOpen hZ hηU hU hJT]⟩
  · rw [M.supp, iUnion_support_restrictOpen hZ hηU hU hJT, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.preimage_comp]
  · rwa [inverseTransformDivisor_ι_eq_restrictOpen]
  · exact fun z hz => ⟨hW, hWs, hT, hTs, hJ, hJT, hZ, hz, hα,
      isCentre_and_weightedOrder_of_restrict sW hTs hJT hZ (u := ηU) hZcl hmem hα hz0 hz M.g
        (by rwa [Category.assoc]) (bijective_functionFieldMap_comp M.g U.ι hbijM hbijU) E hmono⟩
  · intro ξ d z hz hcent hd hval
    haveI := M.isProper
    haveI : AlgebraicGeometry.IsVariety k ((M.g ≫ U.ι) ≫ sW) := by
      rw [Category.assoc]
      exact M.isVariety
    obtain ⟨ξ', p, hcm, hC, hpE, hpF⟩ :=
      exists_isCentre_of_restrict sW (u := ηU) hZcl hz0 hz M.g hbijU hbijM hcentM hcent hd hval
    refine ⟨ξ', IrreducibleCloseds.closureSingleton p, hcm, ?_, ?_, ?_⟩
    · rwa [Category.assoc] at hC
    · exact closure_minimal (Set.singleton_subset_iff.2 hpE) E.idealSheaf.support.isClosed
    · exact fun F hF hFE hsub => hpF F hF hFE (hsub (subset_closure rfl))

end Final

end Restriction

section Neighbourhood

open MMP.Mori Restriction

variable {k : Type uP} [Field k] {W : Scheme.{uP}} {sW : W ⟶ Spec (.of k)} [IsIntegral W]
  [IsLocallyNoetherian W] {T : Divisor W} {J : Finset (MMP.Mori.PrimeDivisor W)}
  {Z : IrreducibleCloseds W}

/-- For an snc divisor `T`, a component of `T` through the generic point of an irreducible
component `Z` of `⋂_{j ∈ J} Tⱼ` is one of the `Tⱼ`. -/
theorem mem_of_genericPoint_mem (hTs : T.IsSNC sW) (hJT : J ⊆ T.support)
    (hZ : Maximal (fun S : Set W => IsIrreducible S ∧ S ⊆ ⋂ E ∈ J, E.support) (Z : Set W))
    {E : MMP.Mori.PrimeDivisor W} (hE : E ∈ T.support)
    (hηE : Z.isIrreducible.genericPoint ∈ (E.support : Set W)) : E ∈ J := by
  classical
  have hmem : ∀ j : J, Z.isIrreducible.genericPoint ∈ (j.1.support : Set W) := fun j =>
    genericPoint_mem_support_of_mem hZ j.2
  have hZcl : (Z : Set W) = closure {Z.isIrreducible.genericPoint} :=
    (Z.isClosed.closure_eq ▸ Z.isIrreducible.isGenericPoint_genericPoint_closure).symm
  obtain ⟨z0, hz0⟩ := exists_localEqs hTs hJT hmem
  have hdim := (span_range_eq_and_ringKrullDim hZ hTs hJT hZcl hmem z0 hz0).2
  obtain ⟨N, w, jj, hw, hjj, -⟩ := hTs.2 Z.isIrreducible.genericPoint
  rw [hw.2] at hdim
  have hNJ : N = Fintype.card J := by exact_mod_cast hdim
  let S := {E : MMP.Mori.PrimeDivisor W // E ∈ T.support ∧ Z.isIrreducible.genericPoint ∈ E.support}
  haveI : Finite S := Finite.of_injective jj hjj
  let ι' : J → S := fun j => ⟨j.1, hJT j.2, hmem j⟩
  have hinj : Function.Injective ι' := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  have hle : Nat.card S ≤ Nat.card J := by
    have := Nat.card_le_card_of_injective jj hjj
    rwa [Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin, hNJ,
      ← Nat.card_eq_fintype_card] at this
  obtain ⟨j, hj⟩ := (hinj.bijective_of_nat_card_le hle).2 ⟨E, hE, hηE⟩
  exact (show j.1 = E from congrArg Subtype.val hj) ▸ j.2

omit [IsIntegral W] [IsLocallyNoetherian W] in
/-- A point lies in `sncComplement T S` exactly when it lies on no component of `T` that does not
contain `S`. -/
theorem mem_sncComplement_iff {S : Set W} {x : W} :
    x ∈ MMP.Fourfold.sncComplement T S ↔ ∀ E ∈ T.support, ¬ S ⊆ E.support → x ∉ E.support := by
  change x ∈ (MMP.Fourfold.sncComplement T S : Set W) ↔ _
  simp [MMP.Fourfold.sncComplement]

/-- In a Noetherian space, a closed set `C` through `x` meets every small enough open
neighbourhood of `x` in a preconnected set. -/
theorem exists_isOpen_isPreconnected_inter {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    {C : Set X} (hC : IsClosed C) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ U : Set X, IsOpen U → x ∈ U → U ⊆ V → _root_.IsPreconnected (C ∩ U) := by
  obtain ⟨hfin, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf hC
  set B := ⋃₀ {Y ∈ MMP.Resolution.componentsOf C | x ∉ Y} with hB
  have hBcl : IsClosed B := (hfin.subset fun Y hY => hY.1).isClosed_sUnion
    fun Y hY => MMP.Resolution.Aux.isClosed_of_mem_componentsOf hC hY.1
  refine ⟨Bᶜ, hBcl.isOpen_compl, fun ⟨Y, hY, hxY⟩ => hY.2 hxY, fun U hU hxU hUV => ?_⟩
  refine isPreconnected_of_forall x fun y hy => ?_
  obtain ⟨Y, hY, hyY⟩ := hcov hy.1
  have hxY : x ∈ Y := by
    by_contra h
    exact hUV hy.2 ⟨Y, ⟨hY, h⟩, hyY⟩
  refine ⟨Y ∩ U, Set.inter_subset_inter_left _ hY.1.2, ⟨hxY, hxU⟩, ⟨hyY, hy.2⟩, ?_⟩
  have heq : closure (Y ∩ U) = Y := le_antisymm
    (closure_minimal Set.inter_subset_left (MMP.Resolution.Aux.isClosed_of_mem_componentsOf hC hY))
    (subset_closure_inter_of_isPreirreducible_of_isOpen hY.1.1.isPreirreducible hU ⟨x, hxY, hxU⟩)
  have hpre : IsPreirreducible (closure (Y ∩ U)) := by
    rw [heq]
    exact hY.1.1.isPreirreducible
  exact (isPreirreducible_iff_closure.1 hpre).isPreconnected

/-- An affine open neighbourhood of the generic point of `Z` meeting only the components `Tⱼ`,
`j ∈ J`, of the snc divisor `T`, in which every intersection of some of the `Tⱼ` is
preconnected. -/
theorem exists_isAffineOpen_nbhd (hW : MMP.Mori.IsVariety k sW) (hTs : T.IsSNC sW)
    (hJT : J ⊆ T.support)
    (hZ : Maximal (fun S : Set W => IsIrreducible S ∧ S ⊆ ⋂ E ∈ J, E.support) (Z : Set W)) :
    ∃ U : W.Opens, Z.isIrreducible.genericPoint ∈ U ∧ IsAffineOpen U ∧
      (∀ E ∈ T.support, (E.support ∩ U).Nonempty → E ∈ J) ∧
      ∀ K ⊆ J, _root_.IsPreconnected ((⋂ E ∈ K, (E.support : Set W)) ∩ U) := by
  haveI : AlgebraicGeometry.IsVariety k sW := hW
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsNoetherian W := ⟨⟩
  have hV : ∀ K : J.powerset, ∃ V : Set W, IsOpen V ∧ Z.isIrreducible.genericPoint ∈ V ∧
      ∀ U : Set W, IsOpen U → Z.isIrreducible.genericPoint ∈ U → U ⊆ V →
        _root_.IsPreconnected ((⋂ E ∈ K.1, (E.support : Set W)) ∩ U) := fun K =>
    exists_isOpen_isPreconnected_inter
      (isClosed_biInter fun E _ => E.idealSheaf.support.isClosed) _
  choose V hVo hηV hVc using hV
  have hZcl : (Z : Set W) = closure {Z.isIrreducible.genericPoint} :=
    (Z.isClosed.closure_eq ▸ Z.isIrreducible.isGenericPoint_genericPoint_closure).symm
  have hmemV : Z.isIrreducible.genericPoint ∈ MMP.Fourfold.sncComplement T (Z : Set W) := by
    refine mem_sncComplement_iff.2 fun E _ hZE hηE => hZE ?_
    rw [hZcl]
    exact closure_minimal (Set.singleton_subset_iff.2 hηE) E.idealSheaf.support.isClosed
  let V0 : W.Opens := ⟨(MMP.Fourfold.sncComplement T (Z : Set W) : Set W) ∩ ⋂ K, V K,
    (MMP.Fourfold.sncComplement T (Z : Set W)).isOpen.inter (isOpen_iInter_of_finite hVo)⟩
  obtain ⟨U, hUa, hηU, hUV⟩ := exists_isAffineOpen_mem_and_subset (U := V0)
    ⟨hmemV, Set.mem_iInter.2 hηV⟩
  refine ⟨U, hηU, hUa, fun E hE ⟨x, hxE, hxU⟩ => ?_, fun K hK => ?_⟩
  swap
  · exact hVc ⟨K, Finset.mem_powerset.2 hK⟩ U U.isOpen hηU
      (fun x hx => Set.mem_iInter.1 (hUV hx).2 _)
  have hZE : (Z : Set W) ⊆ E.support := by
    by_contra hZE
    exact mem_sncComplement_iff.1 (hUV hxU).1 E hE hZE hxE
  exact mem_of_genericPoint_mem hTs hJT hZ hE
    (hZE (Z.isClosed.closure_subset Z.isIrreducible.isGenericPoint_genericPoint_closure.mem))

end Neighbourhood

end MMP.Fourfold.SNCWeight

end
