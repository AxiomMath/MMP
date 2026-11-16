module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.PairClasses
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Discrepancy
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Divisor.PullbackExistence
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParametersCharZero
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# Log canonicity is tested on one log resolution

Let `(X, D)` be a log variety over a perfect field `k`, with canonical divisor
`K_X` of dimension `n` and `K_X + D` `ℝ`-Cartier. If for one log resolution `f : Y ⟶ X` of
`(X, D)` every prime divisor of `Y` exceptional over `X` has discrepancy `≥ -1`, then `(X, D)` is
log canonical. As a consequence, a log terminal log variety is log canonical.

The proof writes `div_Y(f^*ω) + D_Y = f^*(K_X + D)` with `K_X = div_X(ω)`: the coefficients of
`D_Y` are at most one and its support lies in the snc divisor of the log resolution. A divisor
`F` of `k(X)` with nonempty center on `X` has a center on `Y` because `f` is proper, and its
discrepancy over `(X, D)` equals its discrepancy over `(Y, D_Y)` (crepant pull-back). On the
smooth variety `Y` the latter is `≥ -1`, by the discrepancy of the reduced snc pair
`(Y, ∑_{P ∈ S} P)` and the linearity of discrepancies in the boundary.

## Main results

* `MMP.Flips.isLogCanonical_of_isLogResolution`: log canonicity is tested on one log resolution.
* `MMP.Flips.IsLogTerminal.isLogCanonical`: lt implies lc.

## Implementation notes

The source works over `ℂ`; the statements are made over an arbitrary perfect field. Perfectness
is used once: the residue field at a closed point of a smooth variety is finite, hence
separable, over `k`, so the Kähler differentials of the local ring have a basis dual to a
regular system of parameters. The log variety hypothesis on `(X, D)` is the first conjunct of
`MMP.Flips.IsLogResolution` (resp. of `MMP.Flips.IsLogTerminal`). As in
`MMP.Flips.IsLogTerminal`, a discrepancy is a predicate on its value, and the hypothesis bounds
every value `a` with `MMP.Flips.IsDiscrepancy`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 2,
  2.14, 2.15, 2.17.3
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped WithZero

universe u

namespace Proof_lem_mmp_threefold_lc_one_resolution

open MMP.Mori MMP.Flips

/-- A morphism smooth at every point is smooth. -/
private theorem smooth_of_isSmoothScheme {X S : Scheme.{u}} {f : X ⟶ S}
    (h : IsSmoothScheme f) : Smooth f := by
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun U : {U : X.Opens // Smooth (U.ι ≫ f)} => U.1) ?_ fun U => U.2
  rw [← h, MMP.Mori.smoothLocus, sSup_eq_iSup']
  rfl

/-- The pull-back of a nonzero rational form along a morphism inducing an isomorphism of function
fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := pullbackForms_eq hω m τ ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← repr_pullbackFormsAlong hω m τ, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-! ### Dimensions and exceptional divisors -/

/-- In `WithBot ℕ∞`, if `d + c = n` then `d + 2 ≤ n` iff `2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    norm_cast at h
    rw [show ((n : ℕ) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, ← h,
      show (d : WithBot ℕ∞) + 2 = ((d + 2 : ℕ∞) : WithBot ℕ∞) from rfl, WithBot.coe_le_coe]
    exact ENat.add_le_add_iff_left (ne_top_of_le_ne_top (ENat.coe_ne_top n) (h ▸ le_self_add))

/-- A divisor over a variety of dimension `n` is exceptional iff its center has codimension at
least two. -/
private theorem isExceptional_iff_two_le_coheight {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : ProperDivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  unfold ProperDivisorOver.IsExceptional
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff h

/-- The support of `∑_{P ∈ S} a • P` lies in `S`. -/
private theorem support_sum_single_subset {ι M : Type*} [AddCommMonoid M] (S : Finset ι)
    (a : M) : (∑ P ∈ S, Finsupp.single P a).support ⊆ S := by
  classical
  exact Finsupp.support_finsetSum.trans <| Finset.biUnion_subset.mpr fun P hP =>
    Finsupp.support_single_subset.trans (Finset.singleton_subset_iff.mpr hP)

/-- The valuation of a prime divisor `P` of `X`, viewed as a divisor over `X`, is `ord_P`. -/
private theorem valuation_ofPrimeDivisor {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor k hX P).valuation = P.divisorialValuation :=
  Valuation.ext fun φ => by
    change P.divisorialValuation (functionFieldMap (𝟙 X) φ) = _
    rw [functionFieldMap_id_apply]

/-- A divisor over a normal variety which is not exceptional has the valuation of a prime divisor
of the variety. -/
private theorem exists_primeDivisor_divisorialValuation_eq {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) (hD : ¬ D.IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, D.valuation = P.divisorialValuation := by
  obtain ⟨P, hP⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hD
  exact ⟨P, hP.trans (valuation_ofPrimeDivisor hX P)⟩

/-- The minimum in the snc discrepancy formula is `≥ -1` when every coefficient is `≤ 1`. -/
private theorem neg_one_le_inf_snc_bound {ι : Type*} (S : Finset ι) (c : ι → ℚ)
    (hc : ∀ i ∈ S, c i ≤ 1) {P Q : ι → ι → Prop} :
    (-1 : EReal) ≤ (⨅ (i ∈ S) (j ∈ S) (_ : P i j) (_ : Q i j),
        (((1 - c i - c j : ℚ) : ℝ) : EReal)) ⊓ (⨅ i ∈ S, (((1 - c i : ℚ) : ℝ) : EReal)) ⊓ 1 := by
  have hL : ∀ q : ℚ, -1 ≤ q → (-1 : EReal) ≤ ((q : ℝ) : EReal) := fun q hq => by
    simpa using EReal.coe_le_coe_iff.mpr (by exact_mod_cast hq : (-1 : ℝ) ≤ q)
  refine le_inf (le_inf ?_ ?_) ?_
  · refine le_iInf₂ fun i hi => le_iInf₂ fun j hj => le_iInf₂ fun _ _ => hL _ ?_
    linarith [hc i hi, hc j hj]
  · exact le_iInf₂ fun i hi => hL _ (by linarith [hc i hi])
  · simpa using hL 1 (by norm_num)

/-- A variety of dimension `n` with an exceptional divisor over it has `n ≥ 2`. -/
private theorem two_le_of_isExceptional {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {D : DivisorOver k sX} (hD : D.IsExceptional) : 2 ≤ n := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have h := topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)
  rw [hn] at h
  have h0 : 0 ≤ topologicalKrullDim (closure {D.f D.E.genericPoint} : Set X) :=
    Order.krullDim_nonneg_iff.mpr ⟨⟨closure {⟨_, subset_closure rfl⟩},
      isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have : ((Order.coheight (D.f D.E.genericPoint) : ℕ∞) : WithBot ℕ∞) ≤ n :=
    h ▸ le_add_of_nonneg_left h0
  exact_mod_cast ((MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX D).mp hD).trans
    (WithBot.coe_le_coe.mp this)

end Proof_lem_mmp_threefold_lc_one_resolution

namespace MMP.Flips

open MMP.Mori

/-! ### Regular systems of parameters at a generization -/

/-- Let `A → B` be the localization at a prime `p`, `t_i ∈ p` and `δ_i` derivations of `A` dual
to the `t_i`. Then the classes of the `t_i` in the cotangent space of `B` are linearly
independent. -/
theorem linearIndependent_toCotangent_of_derivation {k A B : Type*} [CommRing k]
    [CommRing A] [Algebra k A] [CommRing B] [IsLocalRing B] [Algebra A B] (p : Ideal A)
    [p.IsPrime] [IsLocalization.AtPrime B p] {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → A)
    (ht : ∀ i, t i ∈ p) (δ : ι → Derivation k A A)
    (hδ : ∀ i l, δ i (t l) = if i = l then 1 else 0) :
    ∃ hmem : ∀ i, algebraMap A B (t i) ∈ IsLocalRing.maximalIdeal B,
      LinearIndependent (IsLocalRing.ResidueField B)
        (fun i => (IsLocalRing.maximalIdeal B).toCotangent ⟨algebraMap A B (t i), hmem i⟩) := by
  classical
  have hmB : ∀ a ∈ p, algebraMap A B a ∈ IsLocalRing.maximalIdeal B := fun a ha => by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p B]; exact Ideal.mem_map_of_mem _ ha
  refine ⟨fun i => hmB _ (ht i), ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose b hb using fun l => IsLocalRing.residue_surjective (g l)
  -- `∑ b_l t_l ∈ 𝔪_B²`
  have hsm : ∑ l, b l * algebraMap A B (t l) ∈ IsLocalRing.maximalIdeal B :=
    Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hmB _ (ht l))
  have h2 : ∑ l, b l * algebraMap A B (t l) ∈ IsLocalRing.maximalIdeal B ^ 2 := by
    refine (Ideal.toCotangent_eq_zero (IsLocalRing.maximalIdeal B) ⟨_, hsm⟩).mp ?_
    rw [← hg]
    have : (⟨_, hsm⟩ : IsLocalRing.maximalIdeal B) =
        ∑ l, b l • ⟨algebraMap A B (t l), hmB _ (ht l)⟩ := by
      ext; simp [smul_eq_mul]
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, ← hb l]
    exact (algebraMap_smul (IsLocalRing.ResidueField B) (b l)
      ((IsLocalRing.maximalIdeal B).toCotangent ⟨_, hmB _ (ht l)⟩)).symm
  -- clearing denominators: `w · ∑ a_l t_l ∈ p²` with `w ∉ p`
  obtain ⟨⟨s, hs⟩, hsb⟩ := IsLocalization.exist_integer_multiples p.primeCompl Finset.univ b
  choose a ha using fun l => hsb l (Finset.mem_univ l)
  set α := ∑ l, a l * t l
  have hα : algebraMap A B α ∈ Ideal.map (algebraMap A B) (p ^ 2) := by
    rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal p B]
    have : algebraMap A B α = algebraMap A B s * ∑ l, b l * algebraMap A B (t l) := by
      simp only [α, map_sum, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [ha l, Algebra.smul_def]; ring
    rw [this]; exact Ideal.mul_mem_left _ _ h2
  obtain ⟨⟨⟨β, hβ⟩, ⟨u, hu⟩⟩, hβu⟩ := (IsLocalization.mem_map_algebraMap_iff p.primeCompl B).mp hα
  simp only at hβu
  rw [← map_mul, IsLocalization.eq_iff_exists p.primeCompl] at hβu
  obtain ⟨⟨c, hc⟩, hcu⟩ := hβu
  simp only at hcu
  have hw : (c * u) * α ∈ p ^ 2 := by
    rw [show c * u * α = c * β by rw [← hcu]; ring]; exact Ideal.mul_mem_left _ _ hβ
  -- applying `δ_i`, which maps `p²` into `p`
  have hδp : ∀ x ∈ p ^ 2, δ i x ∈ p := by
    intro x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact add_mem (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_right _ _ hy)
    · rw [map_add]; exact add_mem hx hy
  have hαp : α ∈ p := Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (ht l)
  have hcu' : c * u ∉ p := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hc hu
  have hδα : δ i α ∈ p := by
    have h := hδp _ hw
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h
    have := (Submodule.add_mem_iff_left _ (Ideal.mul_mem_right _ _ hαp)).mp h
    exact (Ideal.IsPrime.mem_or_mem ‹_› this).resolve_left hcu'
  have hai : a i ∈ p := by
    have : δ i α = a i + ∑ l, t l * δ i (a l) := by
      simp only [α, map_sum, Derivation.leibniz, smul_eq_mul, hδ, Finset.sum_add_distrib,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [this] at hδα
    exact (Submodule.add_mem_iff_left _ (Ideal.sum_mem _ fun l _ =>
      Ideal.mul_mem_right _ _ (ht l))).mp hδα
  have hbi : b i ∈ IsLocalRing.maximalIdeal B := by
    have h1 := hmB _ hai
    rw [ha i, Algebra.smul_def] at h1
    have hunit : IsUnit (algebraMap A B s) := IsLocalization.map_units B ⟨s, hs⟩
    exact (Ideal.IsPrime.mem_or_mem inferInstance h1).resolve_left
      fun h => (IsLocalRing.mem_maximalIdeal _).mp h hunit
  rw [← hb i]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hbi

/-- A family in the maximal ideal of a regular local ring whose classes in the cotangent space
are linearly independent is part of a regular system of parameters. -/
theorem exists_isRegularSystemOfParameters_extend {B : Type*} [CommRing B]
    [IsRegularLocalRing B] {ι : Type*} [Fintype ι] (t : ι → B)
    (hmem : ∀ i, t i ∈ IsLocalRing.maximalIdeal B)
    (hli : LinearIndependent (IsLocalRing.ResidueField B)
      (fun i => (IsLocalRing.maximalIdeal B).toCotangent ⟨t i, hmem i⟩)) :
    ∃ (M : ℕ) (w : Fin M → B) (c : ι → Fin M), IsRegularSystemOfParameters w ∧
      Function.Injective c ∧ ∀ i, w (c i) = t i := by
  classical
  let eι := Fintype.equivFin ι
  let v₀ : Fin (Fintype.card ι) → IsLocalRing.CotangentSpace B :=
    fun i => (IsLocalRing.maximalIdeal B).toCotangent ⟨t (eι.symm i), hmem _⟩
  have hv₀ : LinearIndependent (IsLocalRing.ResidueField B) v₀ := hli.comp _ eι.symm.injective
  obtain ⟨e, v, -, hvli, hvsp⟩ :=
    MMP.Flips.ResolutionInputs.exists_sumElim_basis v₀ hv₀ Set.univ (by simp)
  choose r hr using fun j => Ideal.toCotangent_surjective (IsLocalRing.maximalIdeal B) (v j)
  let u : Fin (Fintype.card ι) ⊕ Fin e → IsLocalRing.maximalIdeal B :=
    Sum.elim (fun i => ⟨t (eι.symm i), hmem _⟩) r
  have hu : (IsLocalRing.maximalIdeal B).toCotangent ∘ u = Sum.elim v₀ v := by
    funext a; cases a with
    | inl i => rfl
    | inr j => exact hr j
  let w : Fin (Fintype.card ι + e) → B := fun m => (u (finSumFinEquiv.symm m) : B)
  refine ⟨_, w, fun i => finSumFinEquiv (Sum.inl (eι i)), ⟨?_, ?_⟩, ?_, ?_⟩
  · have hspan : Submodule.span B (Set.range u) = ⊤ := by
      rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff, ← Set.range_comp, hu]
      exact top_le_iff.mp hvsp
    have hw : Set.range w = (IsLocalRing.maximalIdeal B).subtype '' Set.range u := by
      rw [← Set.range_comp]
      exact finSumFinEquiv.symm.surjective.range_comp (Subtype.val ∘ u)
    change Submodule.span B (Set.range w) = _
    rw [hw, ← Submodule.map_span, hspan, Submodule.map_top, Submodule.range_subtype]
  · rw [← IsRegularLocalRing.spanFinrank_maximalIdeal,
      IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
      Module.finrank_eq_card_basis (Module.Basis.mk hvli hvsp)]
    simp
  · intro i j h; simpa using h
  · intro i; simp [w, u]

end MMP.Flips

namespace Proof_lem_mmp_threefold_lc_one_resolution

open MMP.Mori MMP.Flips

/-- At a closed point of a scheme smooth over a perfect field, a regular system
of parameters has a dual family of derivations of the local ring. -/
private theorem exists_derivation_dual {k : Type u} [Field k] [PerfectField k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [Smooth sY] (x : Y) (hx : IsClosed ({x} : Set Y)) {N : ℕ}
    (z : Fin N → Y.presheaf.stalk x) (hz : IsRegularSystemOfParameters z) :
    letI := MMP.Mori.stalkAlgebra sY x
    ∃ δ : Fin N → Derivation k (Y.presheaf.stalk x) (Y.presheaf.stalk x),
      ∀ i l, δ i (z l) = if i = l then 1 else 0 := by
  classical
  let := MMP.Mori.stalkAlgebra sY x
  obtain ⟨_, _, _⟩ := MMP.Flips.ResolutionInputs.stalk_facts sY x
  have : Module.Finite k (IsLocalRing.ResidueField (Y.presheaf.stalk x)) :=
    MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sY x hx
  have : Algebra.FormallyUnramified k (IsLocalRing.ResidueField (Y.presheaf.stalk x)) :=
    Algebra.FormallyUnramified.of_isSeparable _ _
  obtain ⟨hz0, hli, -⟩ := MMP.Flips.ResolutionInputs.cotangent_basis_of_regular z hz.1 hz.2
  have hli' := MMP.Flips.ResolutionInputs.linearIndependent_tmul_D k z hz0 hli
  have hsp' := MMP.Flips.ResolutionInputs.span_tmul_D k z hz.1
  have : Module.Projective (Y.presheaf.stalk x) Ω[Y.presheaf.stalk x⁄k] :=
    ((Algebra.formallySmooth_iff _ _).mp ‹_›).1
  have : Module.Flat (Y.presheaf.stalk x) Ω[Y.presheaf.stalk x⁄k] := Module.Flat.of_projective
  have hbij : Function.Bijective (Finsupp.linearCombination (Y.presheaf.stalk x)
      (fun i => KaehlerDifferential.D k (Y.presheaf.stalk x) (z i))) := by
    apply Module.IsLocalRing.linearCombination_bijective_of_flat
    refine ⟨hli', ?_⟩
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact top_le_iff.mp hsp'
  let b := MMP.Flips.ResolutionInputs.basisOfBijective _ hbij
  refine ⟨fun i => (b.coord i).compDer (KaehlerDifferential.D k (Y.presheaf.stalk x)),
    fun i l => ?_⟩
  change b.coord i (KaehlerDifferential.D k _ (z l)) = _
  rw [← MMP.Flips.ResolutionInputs.basisOfBijective_apply _ hbij l]
  change b.coord i (b l) = _
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

/-! ### Simple normal crossings at closed points and at all points -/

/-- On a smooth variety over a perfect field, an snc divisor in the sense of
`MMP.Flips.IsSNCDivisor` (transversality at closed points) is snc in the sense of
`MMP.Mori.DivisorWithCoeffs.IsSNC` (transversality at every point). -/
theorem _root_.MMP.Flips.IsSNCDivisor.isSNC {k : Type u} [Field k] [PerfectField k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian Y] [CompactSpace Y]
    (hY : AlgebraicGeometry.IsVariety k sY) (hsm : IsSmoothScheme sY) {G : Divisor Y}
    (hG : IsSNCDivisor sY G) : DivisorWithCoeffs.IsSNC sY G := by
  classical
  have : Smooth sY := smooth_of_isSmoothScheme hsm
  refine ⟨fun E hE => hG.2.1 E hE, fun y => ?_⟩
  -- a closed point `x` specializing `y`
  obtain ⟨x, hxy, hx⟩ : ∃ x ∈ closure ({y} : Set Y), IsClosed ({x} : Set Y) :=
    isClosed_closure.exists_closed_singleton ⟨y, subset_closure rfl⟩
  have h : y ⤳ x := specializes_iff_mem_closure.mpr hxy
  obtain ⟨N, z, j, hz, hj, hI⟩ := hG.2.2 x hx
  let := MMP.Mori.stalkAlgebra sY x
  obtain ⟨δ, hδ⟩ := exists_derivation_dual sY x hx z hz
  letI := (Y.presheaf.stalkSpecializes h).hom.toAlgebra
  haveI := MMP.Intersection.isLocalization_stalkSpecializes h
  haveI := AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth_over_field sY y
  -- the components of `G` through `y` pass through `x`
  have hTx : ∀ E : {E : MMP.Mori.PrimeDivisor Y // E ∈ G.support ∧ y ∈ E.support},
      x ∈ E.1.support := fun E => h.mem_closed
        (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure) E.2.2
  haveI : Finite {E : MMP.Mori.PrimeDivisor Y // E ∈ G.support ∧ y ∈ E.support} :=
    Finite.of_injective (fun E => (⟨E.1, E.2.1⟩ : {E // E ∈ G.support}))
      (fun a b hab => Subtype.ext (congrArg Subtype.val hab :))
  haveI := Fintype.ofFinite {E : MMP.Mori.PrimeDivisor Y // E ∈ G.support ∧ y ∈ E.support}
  let jT : {E : MMP.Mori.PrimeDivisor Y // E ∈ G.support ∧ y ∈ E.support} → Fin N :=
    fun E => j ⟨E.1, E.2.1, hTx E⟩
  have hjT : Function.Injective jT := fun E E' hEE' => Subtype.ext (Subtype.mk.inj (hj hEE'))
  have htp : ∀ E, z (jT E) ∈ MMP.Intersection.primeOfSpecializes h := fun E => by
    have hle := (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes E.1.idealSheaf h).mp
      (by simpa using E.2.2)
    exact hle ((hI ⟨E.1, E.2.1, hTx E⟩).symm ▸ Ideal.mem_span_singleton_self _)
  obtain ⟨hmem, hli⟩ := linearIndependent_toCotangent_of_derivation (B := Y.presheaf.stalk y)
    (MMP.Intersection.primeOfSpecializes h) (fun E => z (jT E)) htp (fun E => δ (jT E))
    (fun E E' => by rw [hδ]; simp [hjT.eq_iff])
  obtain ⟨M, w, c, hw, hc, hwc⟩ := exists_isRegularSystemOfParameters_extend _ hmem hli
  refine ⟨M, w, c, hw, hc, fun E => ?_⟩
  rw [MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes _ h, hI ⟨E.1, E.2.1, hTx E⟩,
    Ideal.map_span, Set.image_singleton, hwc E]
  rfl

/-! ### Discrepancies on a smooth variety with an snc boundary -/

/-- Splitting a sum over `Fin (m + #S)` built by `Fin.append` into its `Fin m` part and a sum
over the finset `S`, reindexed along `S.equivFin`. -/
private theorem sum_append_equivFin {ι α : Type*} (S : Finset ι) {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → α) (c : ι → ℝ) (B : ι → α) (φ : α → ℝ) :
    ∑ i, Fin.append r (fun i => c (S.equivFin.symm i)) i *
        φ (Fin.append L (fun i => B (S.equivFin.symm i)) i) =
      ∑ j, r j * φ (L j) + ∑ P ∈ S, c P * φ (B P) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [Fintype.sum_equiv S.equivFin.symm _ (fun P : S => c P * φ (B P)) fun _ => rfl,
    Finset.sum_coe_sort S fun P => c P * φ (B P)]

/-- Let `Y` be a smooth variety over a perfect field, `G` an snc divisor on `Y`
and `D_Y` an `ℝ`-divisor supported on `G` with coefficients at most one. Then every
discrepancy `a(F, D_Y)` of a divisor `F` of `k(Y)` with nonempty center is at least `-1`. -/
private theorem neg_one_le_of_isSNCDivisor {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [LocallyOfFiniteType sY] (hY : IsNormalVariety k sY)
    (hsm : IsSmoothScheme sY)
    {G : Divisor Y} (hG : IsSNCDivisor sY G) {n : ℕ} {KY : Divisor Y} {DY : RDivisor Y}
    (hsupp : ∀ P, DY.coeff P ≠ 0 → G.coeff P = 1) (hc : ∀ P, DY.coeff P ≤ 1)
    {v : Valuation Y.functionField ℤᵐ⁰} {b : ℝ} (hb : MMP.Flips.IsDiscrepancy sY n KY DY v b) :
    -1 ≤ b := by
  classical
  obtain ⟨hKY, -, -, E, τ, m, r, L, hEv, hτK, hw⟩ := id hb
  subst hτK
  obtain ⟨-, hn, hτ0, hLc, hsum, L', hpb, hbval⟩ := hw
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have : CompactSpace E.Y := (E.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  by_cases hex : E.toDivisorOver.IsExceptional
  swap
  · -- a divisor of `Y` itself: the discrepancy is `-coeff_P(D_Y) ≥ -1`
    obtain ⟨P, hP⟩ := exists_primeDivisor_divisorialValuation_eq hY E.toDivisorOver hex
    rw [← hEv, show E.valuation = P.divisorialValuation from hP] at hb
    linarith [hb.eq_neg_coeff, hc P]
  -- the components of `G`, their pull-backs to the model of `E`, and the reduced boundary
  set S : Finset (MMP.Mori.PrimeDivisor Y) := G.support
  have hcart := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  choose B hB using fun P : MMP.Mori.PrimeDivisor Y =>
    MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hcart (Finsupp.single P (1 : ℤ)))
  have hB0 : ∀ P, 0 ≤ (B P).coeff E.E := fun P =>
    MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤) (hcart _)
      (fun P' _ => by
        rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]; split_ifs <;> simp)
      (hB P) E.E ((E.E.genericPoint_mem_iff _).mp trivial)
  have hDYS : ∀ P, P ∉ S → DY.coeff P = 0 := fun P hP => by
    by_contra h
    exact hP (Finsupp.mem_support_iff.mpr (by
      rw [← DivisorWithCoeffs.coeff_apply, hsupp P h]; exact one_ne_zero))
  set Δ₁ : QDivisor Y := ∑ P ∈ S, Finsupp.single P (1 : ℚ)
  have hΔ₁ : ∀ P, Δ₁.coeff P = if P ∈ S then 1 else 0 := fun P => by
    simp [Δ₁, DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
  -- the log discrepancy of `E` with respect to `(Y, Δ₁)`, computed with the presentation
  -- `div(τ) + Δ₁ = ∑ r_j L_j + ∑_{P ∈ S} (1 - coeff_P(D_Y)) P`
  let e := S.equivFin.symm
  let r₁ : Fin (m + S.card) → ℝ := Fin.append r (fun i => 1 - DY.coeff (e i))
  let C : Fin (m + S.card) → Divisor Y :=
    Fin.append L (fun i => Finsupp.single (e i : MMP.Mori.PrimeDivisor Y) 1)
  let C' : Fin (m + S.card) → Divisor E.Y := Fin.append L' (fun i => B (e i))
  have hb₁ : MMP.Intersection.IsLogDiscrepancy sY n (QDivisor.toRDivisor Δ₁) E.toDivisorOver
      (1 + (E.toDivisorOver.ordPullback τ : ℝ) - ∑ i, r₁ i * (C' i).coeff E.E) := by
    refine ⟨hY, E.isProper, τ, hτ0, ⟨divisorOfForm τ, hKY, fun Γ => coeff_divisorOfForm τ Γ⟩,
      m + S.card, r₁, C, C', fun i => hcart _, fun Γ => ?_, fun i => ?_, rfl⟩
    · have h1 := congrArg (fun B : RDivisor Y => B.coeff Γ) hsum
      simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
        coeff_sum_smul_toRDivisor] at h1
      simp only [r₁, C, e]
      rw [sum_append_equivFin S r L (fun P => 1 - DY.coeff P) (fun P => Finsupp.single P 1)
        fun G : Divisor Y => ((G.coeff Γ : ℤ) : ℝ)]
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, Int.cast_ite, Int.cast_one,
        Int.cast_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq'] at h1 ⊢
      rw [show (QDivisor.toRDivisor Δ₁) Γ = ((Δ₁.coeff Γ : ℚ) : ℝ) from
        QDivisor.coeff_toRDivisor Δ₁ Γ, hΔ₁]
      by_cases hΓ : Γ ∈ S
      · simp only [hΓ, if_true, Rat.cast_one]
        linarith
      · simp only [hΓ, if_false, Rat.cast_zero, add_zero]
        have := hDYS Γ hΓ
        rw [DivisorWithCoeffs.coeff_apply] at this
        linarith
    · induction i using Fin.addCases with
      | left j => simpa only [C, C', Fin.append_left] using hpb j
      | right j =>
        simp only [C, C', Fin.append_right]
        exact ⟨MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp E.f _, hB (e j)⟩
  -- the Kollár–Mori discrepancy of `E` over the snc pair `(Y, Δ₁)` is `≥ -1`
  have hpair : IsPairWith sY n (divisorOfForm τ) Δ₁ :=
    ⟨hY, hKY, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩
  obtain ⟨a₁, ha₁⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair.isPair hKY E.toDivisorOver
  have hb₁eq := ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy ha₁ _).mp hb₁).2
  have ha₁ge : (-1 : ℝ) ≤ a₁ := by
    have hn2 : 2 ≤ n := two_le_of_isExceptional hY hn hex
    have h := MMP.Mori.discrep_le hex ha₁
    rw [MMP.Mori.discrep_eq_of_isSNC sY hY hsm hn2 hKY S (support_sum_single_subset S 1)
      ((MMP.Flips.IsSNCDivisor.isSNC hY.1 hsm hG).of_support_subset (support_sum_single_subset S 1))
      (fun P hP => by rw [hΔ₁, if_pos hP])] at h
    have : ((-1 : ℝ) : EReal) ≤ ((a₁ : ℝ) : EReal) := by
      simpa using (neg_one_le_inf_snc_bound S Δ₁.coeff
        (fun P hP => by rw [hΔ₁, if_pos hP])).trans h
    exact_mod_cast EReal.coe_le_coe_iff.mp this
  -- comparison of the two presentations
  have hcomp : 1 + (E.toDivisorOver.ordPullback τ : ℝ) - ∑ i, r₁ i * (C' i).coeff E.E =
      1 + b - ∑ P ∈ S, (1 - DY.coeff P) * ((B P).coeff E.E : ℝ) := by
    simp only [r₁, C', e]
    rw [sum_append_equivFin S r L' (fun P => 1 - DY.coeff P) B
      fun G : Divisor E.Y => ((G.coeff E.E : ℤ) : ℝ), hbval]
    ring
  have hnonneg : 0 ≤ ∑ P ∈ S, (1 - DY.coeff P) * ((B P).coeff E.E : ℝ) :=
    Finset.sum_nonneg fun P _ => mul_nonneg (by linarith [hc P]) (by exact_mod_cast hB0 P)
  linarith

/-! ### Lifting divisors over `X` to a proper birational model -/

/-- For a proper birational morphism `f : Y ⟶ X` from a normal variety, every divisor `D` over
`X` has the valuation of a divisor `E` over `Y`, read on `k(X)` through `f^*`. -/
private theorem exists_properDivisorOver_comap_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y] {f : Y ⟶ X}
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) [IsProper f]
    (D : ProperDivisorOver k sX) :
    haveI : IsDominant f := hf.isDominant
    ∃ E : ProperDivisorOver k (f ≫ sX), E.valuation.comap (functionFieldMap f) = D.valuation := by
  have : IsDominant f := hf.isDominant
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have hbW := hf.functionFieldMap_bijective
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap f) hbW
  let ξ : Valuation Y.functionField ℤᵐ⁰ := D.valuation.comap (e.symm : Y.functionField →+* _)
  have hξ : ξ.comap (functionFieldMap f) = D.valuation := by
    ext t
    exact congrArg D.valuation (e.symm_apply_apply t)
  -- `ξ` dominates the local ring of a point of `Y` (valuative criterion for `f`)
  obtain ⟨x, h1, h2⟩ : ∃ x : Y, (∀ a : Y.presheaf.stalk x,
      ξ (algebraMap _ Y.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x),
        ξ (algebraMap _ Y.functionField a) < 1 := by
    set z := D.f D.E.genericPoint
    have hw : ∀ b : X.presheaf.stalk z,
        ξ (functionFieldMap f (algebraMap _ X.functionField b)) =
          D.valuation (algebraMap _ X.functionField b) := fun b => by
      simpa only [Valuation.comap_apply] using
        congrArg (fun v => v (algebraMap _ X.functionField b)) hξ
    let R := ξ.valuationSubring
    let φ : X.presheaf.stalk z →+* R :=
      ((functionFieldMap f).comp (algebraMap (X.presheaf.stalk z) X.functionField)).codRestrict R
        fun b => (ξ.mem_valuationSubring_iff _).2 (by
          rw [RingHom.comp_apply, hw]
          exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D.toDivisorOver z rfl _)
    have hgen : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
    have hex : ValuativeCriterion.Existence f := by
      have h : @IsProper _ _ f := inferInstance
      rw [IsProper.eq_valuativeCriterion] at h
      exact h.1.1.1.existence
    let S : ValuativeCommSq f :=
      { R := R
        K := Y.functionField
        i₁ := Y.fromSpecStalk (genericPoint Y)
        i₂ := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk z
        commSq := ⟨by
          rw [← functionFieldMap_fromSpecStalk f,
            ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
            ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
          rfl⟩ }
    obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
    have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫ l =
        Y.fromSpecStalk (genericPoint Y) := hl₁
    set x := l (IsLocalRing.closedPoint R)
    have hx : genericPoint Y ⤳ x := (genericPoint_spec Y).specializes trivial
    let g := Scheme.stalkClosedPointTo l
    have hg : g ≫ CommRingCat.ofHom (algebraMap R Y.functionField) =
        Y.presheaf.stalkSpecializes hx := by
      apply Spec.map_injective
      apply (cancel_mono (Y.fromSpecStalk x)).mp
      rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    have hga : ∀ a : Y.presheaf.stalk x,
        algebraMap _ Y.functionField a = ((g.hom a : R) : Y.functionField) := fun a =>
      (congrArg (fun q => q.hom a) hg).symm
    refine ⟨x, fun a => ?_, fun a ha => ?_⟩
    · rw [hga]; exact (g.hom a).2
    · rw [hga]
      exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
        (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit g.hom a hu))
  -- `ξ` is a divisor of `k(Y)`: `ord_E` on `D.Y`, along `k(Y) ≅ k(X) ≅ k(D.Y)`
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (f ≫ sX) ξ := by
    have := D.isIntegral
    have := D.isNormal
    have := D.isLocallyNoetherian
    have := D.isDominant
    refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ?_⟩
    let := MMP.Mori.functionFieldAlgebra sX
    let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    let := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
    let eP := MMP.Mori.functionFieldAlgEquiv sX f hbW
    let eY :=
      MMP.Mori.functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eP.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbW.2 t
    have hs := congrArg (fun v => v s) hξ
    simp only [Valuation.comap_apply] at hs
    have h1 : eP.symm (functionFieldMap f s) = s := eP.symm_apply_apply s
    change ξ (functionFieldMap f s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap f s)))
    rw [h1, hs]
    rfl
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (f ≫ sX) hdiv x h1 h2
  exact ⟨D', by rw [hv, hξ]⟩

/-! ### Exceptional divisors -/

/-- A divisor `(Y, f, E)` over `X` which is not exceptional has the valuation of a prime divisor
of `X`. -/
private theorem exists_primeDivisor_valuation_eq_of_not_isExceptional {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) (E : ProperDivisorOver k sX) (hE : ¬ E.IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, E.valuation = P.divisorialValuation :=
  exists_primeDivisor_divisorialValuation_eq hX E.toDivisorOver fun h =>
    hE <| (isExceptional_iff_two_le_coheight hn E).mpr <|
      (MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX _).mp h

end Proof_lem_mmp_threefold_lc_one_resolution

namespace MMP.Flips

open MMP.Mori
open Proof_lem_mmp_threefold_lc_one_resolution

/-- Let `(X, D)` be a log variety over a perfect field `k`, `K` a canonical divisor
of `X` of dimension `n` with `K + D` `ℝ`-Cartier, and `f : Y ⟶ X` a log resolution of `(X, D)`.
If every prime divisor `E` of `Y` exceptional over `X` has discrepancy `a(E, D) ≥ -1`, then
`(X, D)` is log canonical. -/
@[mmp "lem_mmp_threefold_lc_one_resolution"]
public theorem isLogCanonical_of_isLogResolution {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {D : RDivisor X}
    (hK : K.IsCanonicalDivisor sX n) (hKD : IsCartierCombination (Divisor.toRDivisor K + D))
    {Y : Scheme.{u}} (f : Y ⟶ X) (hf : IsLogResolution sX D f)
    (hdisc : ∀ (hY : IsNormalVariety k (f ≫ sX)) (hb : IsBirationalMorphism f) (hp : IsProper f)
      (E : Mori.PrimeDivisor Y),
      (ProperDivisorOver.mk ⟨Y, f, hY, hb, E⟩ hp).IsExceptional →
      ∀ a : ℝ, IsDiscrepancy sX n K D (ProperDivisorOver.mk ⟨Y, f, hY, hb, E⟩ hp).valuation a →
        -1 ≤ a) :
    IsLogCanonical sX n K D := by
  classical
  obtain ⟨hlv, hYvar, hYsm, hfp, hfb, G, -, hGiff, hGsnc⟩ := id hf
  have hX : IsNormalVariety k sX := hlv.isNormalVariety
  refine ⟨hlv, hK, hKD, fun F hF a ha => ?_⟩
  obtain ⟨-, -, -, E₀, ω, m, r, L, hE₀F, hωK, hw⟩ := id ha
  subst hωK
  have hω0 : ω ≠ 0 := hw.2.2.1
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  -- instances on `Y`
  haveI : IsIntegral Y := hYvar.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hYvar.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : Smooth (f ≫ sX) := smooth_of_isSmoothScheme hYsm
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI : IsNormal Y := AlgebraicGeometry.isNormal_of_smooth (f ≫ sX)
  haveI : CompactSpace Y := hYvar.toQuasiCompact.compactSpace_of_compactSpace
  haveI := hfp
  haveI : IsDominant f := hfb.isDominant
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hYvar
  have hY : IsNormalVariety k (f ≫ sX) := ⟨hYvar, inferInstance⟩
  -- the crepant boundary `D_Y`: `div_Y(f^*ω) + D_Y = f^*(K_X + D)`
  obtain ⟨GP, hGP, -⟩ := existsUnique_isRCartierPullback f hKD
  set σ := pullbackRationalPluriForms sX f ω with hσ
  set DY : RDivisor Y := GP - Divisor.toRDivisor (divisorOfForm σ) with hDYdef
  have hDY : IsRCartierPullback f (Divisor.toRDivisor (divisorOfForm ω) + D)
      (Divisor.toRDivisor (divisorOfForm σ) + DY) := by
    rw [hDYdef, add_sub_cancel]; exact hGP
  have hbij := hfb.functionFieldMap_bijective
  have hσ0 : σ ≠ 0 := pullbackRationalPluriForms_ne_zero f hbij
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn) hω0
  have hnY : topologicalKrullDim Y = n := by
    rw [← hn]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hfb).symm
  have hKY : (divisorOfForm σ).IsCanonicalDivisor (f ≫ sX) n := by
    obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hYsm hnY
    exact hK₀.of_linearlyEquivalent (by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀ hσ0)
  have hcrep := isDiscrepancy_comap_functionFieldMap_iff hX hω0 hK hKD f hY hfb hDY hKY
  -- the boundary `D_Y` is supported on the snc divisor `G`, with coefficients `≤ 1`
  have hKDY : IsCartierCombination (Divisor.toRDivisor (divisorOfForm σ) + DY) := by
    obtain ⟨m', r', L', L'', hLc, -, hpb, heq⟩ := hDY
    refine ⟨m', r', L'', fun j => (hpb j).2.isCartier (hLc j), ?_⟩
    rw [heq]
    simp only [toRDivisor_eq_mapCoeffs]
  have hcoeff : ∀ P, DY.coeff P ≤ 1 := by
    intro P
    let EP : ProperDivisorOver k (f ≫ sX) :=
      ⟨DivisorOver.ofPrimeDivisor k hY P, (inferInstance : IsProper (𝟙 Y))⟩
    have h1 := isDiscrepancy_divisorialValuation hY σ hσ0 hKY hKDY P
    rw [← valuation_ofPrimeDivisor hY P] at h1
    have h2 := (hcrep EP _).mpr h1
    have hv : EP.valuation.comap (functionFieldMap f) =
        (ProperDivisorOver.mk ⟨Y, f, hY, hfb, P⟩ hfp).valuation := by
      ext g
      change P.divisorialValuation (functionFieldMap (𝟙 Y) (functionFieldMap f g)) =
        P.divisorialValuation (functionFieldMap f g)
      rw [functionFieldMap_id_apply]
    rw [hv] at h2
    by_cases hex : (ProperDivisorOver.mk ⟨Y, f, hY, hfb, P⟩ hfp).IsExceptional
    · linarith [hdisc hY hfb hfp P hex _ h2]
    · obtain ⟨Q, hQ⟩ := exists_primeDivisor_valuation_eq_of_not_isExceptional hX hn _ hex
      rw [hQ] at h2
      have := h2.eq_neg_coeff
      linarith [(hlv.isBoundary Q).2]
  have hsupp : ∀ P, DY.coeff P ≠ 0 → G.coeff P = 1 := by
    obtain ⟨Ex, aE, GP', hEx, hGP', -, hform⟩ := discrepancy_formula hX D ω hω0 hK hKD f hY hfb
    have hGG : GP' = GP := IsRCartierPullback.eq f hGP' hGP
    intro P hP
    refine (hGiff P).mpr ?_
    by_cases hex : IsExceptionalPrimeDivisor sX f P
    · exact Or.inr hex
    · left
      have hPEx : P ∉ Ex := fun h => hex ((hEx P).mp h)
      have h := DFunLike.congr_fun hform P
      simp only [Finsupp.add_apply, Finsupp.coe_finset_sum, Finset.sum_apply,
        Finsupp.single_apply, Finset.sum_ite_eq', hPEx, if_false, add_zero, hGG] at h
      rw [DivisorWithCoeffs.coeff_apply] at hP ⊢
      rw [← hσ] at h
      rw [hDYdef, Finsupp.sub_apply, ← h] at hP
      simpa using hP
  -- the divisor `F` has a center on `Y`
  obtain ⟨E, hE⟩ := exists_properDivisorOver_comap_eq hY hfb E₀
  have haY := (hcrep E a).mp (by rw [hE, hE₀F]; exact ha)
  exact neg_one_le_of_isSNCDivisor hY hYsm hGsnc hsupp hcoeff haY

/-- A log terminal log variety `(X, D)` over a perfect field, with canonical divisor
`K` of dimension `n`, is log canonical. -/
@[mmp "lem_fa2_lt_implies_lc"]
public theorem IsLogTerminal.isLogCanonical {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {D : RDivisor X}
    (h : IsLogTerminal sX n K D) :
    IsLogCanonical sX n K D := by
  obtain ⟨-, hK, hKD, Y, f, hf, hlt⟩ := h
  exact isLogCanonical_of_isLogResolution sX hK hKD f hf fun hY hb hp E hE a ha => by
    linarith [hlt hY hb hp E hE (1 + a) ⟨a, ha, rfl⟩]

end MMP.Flips

end
