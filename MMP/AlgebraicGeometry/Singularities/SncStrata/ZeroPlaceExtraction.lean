module
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Resolution.ZariskiSequence
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionCenters
public import MMP.AlgebraicGeometry.Resolution.ZariskiSequenceBasic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical

/-!
# Extracting an snc zero place by stratum blow-ups

Let `X` be a smooth projective variety over an algebraically closed field `k` of characteristic
zero and `B` an effective snc boundary on `X`, with coefficient-one locus
`D₀ = ⋃_{coeff_P B = 1} P`. Let `E` be an exceptional divisor over `X` with log discrepancy
`a(E; X, B) = 0`. Then `E` appears as a prime divisor `E_W` on a smooth projective model
`p : W ⟶ X` obtained by finitely many blow-ups of strata of the (total transform of the)
coefficient-one boundary, each centre containing the centre of `E` on the model being blown up.
Moreover:

* every `p`-exceptional prime of `W` has log discrepancy zero over `(X, B)`;
* for every snc closed subset `S ⊆ X` containing `Supp B`, its preimage `p⁻¹(S)` is again an
  snc closed subset of `W`; in particular the total transform of a divisor having simple normal
  crossings with `B` is snc;
* for every effective `ℚ`-Cartier `ℚ`-divisor `A ≤ B` with no component in `⌊B⌋`, the pull-back
  `p^*A` has coefficient zero at every `p`-exceptional prime.

One follows a boundary-compatible extraction sequence for `E`. A step changing the centre of `E`
creates a prime containing that centre; positivity of its log discrepancy would force
`a(E; X, B) > 0` by the snc valuation formula, so by the blow-up discrepancy formula the centre
is a stratum of coefficient-one components, and it may be replaced by the closure of that
stratum. Stratum blow-ups preserve snc, every new prime is crepant with coefficient one, and a
stratum of `D₀` has its generic point off every other component of `B`, hence off `Supp A`.

## Main results

* `MMP.Fourfold.exists_stratumBlowups_valuation_eq_of_isLogDiscrepancy_eq_zero`.
* `MMP.Fourfold.closure_singleton_mem_componentsOf_of_isSNC`: a point of codimension `|T|` on
  every component `G ∈ T` of an snc divisor is the generic point of a smooth component of
  `⋂_{G ∈ T} G`, with ideal `∑_{G ∈ T} I_G` along it.
* `MMP.Fourfold.isDiscrepancy_excE_neg_one`: the exceptional divisor of the blow-up of such a
  stratum, over a boundary with coefficient one along the `G ∈ T`, has discrepancy `-1`.
* `MMP.Fourfold.exists_properDivisorOver_comap_valuation_eq`: the valuation of a divisor over `X`
  is realized by a proper divisor over any normal proper birational model receiving `Spec` of its
  valuation ring.
* `MMP.Mori.PrimeDivisor.exists_localEquation_of_isRegularLocalRing`: at a point `x` with regular
  local ring, a prime divisor `Γ ∋ x` has a local equation `π` with `I_{Γ,x} = (π)` and
  `ord_{Γ'} π = [Γ' = Γ]` for every prime divisor `Γ' ∋ x`.
* `MMP.Mori.QDivisor.IsPullback.coeff_eq_zero_of_notMem`: a pull-back of a `ℚ`-Cartier divisor
  has coefficient zero along a prime divisor whose generic point maps off the support.

## Implementation notes

The composites of stratum blow-ups, together with the centre of `E` on each model, are
described as the smallest class of pairs `(q : Y ⟶ X, y ∈ Y)` that contains `(𝟙 X, x)` for every
`x ∈ X`, is closed under precomposition with isomorphisms, and is closed under passing from
`(q, π y)` to `(π ≫ q, y)` for `π = blowUpToBase Z`, where `Z` is the reduced ideal of a stratum
of `q⁻¹(D₀)` with `π y ∈ Z`. The conclusion is that `(p, ξ_{E_W})` lies in this class, with
`ξ_{E_W}` the generic point of `E_W`; then the condition `π y ∈ Z` says that every centre contains
the centre of `E`. "`E` appears on `W`" is equality of the valuations of `k(X)` given by `E` and
by `(W, p, E_W)`. The divisor `E` over `X` is a `MMP.Flips.ProperDivisorOver`, exceptional in
the sense `MMP.Flips.ProperDivisorOver.IsExceptional` (centre of codimension at least two); the
log discrepancy is `MMP.Intersection.IsLogDiscrepancy`. "An additional divisor snc with `B`" is
an snc closed subset `S ⊇ Supp B` (`MMP.Resolution.IsSNCClosedSubset`), and its total transform
has support `p⁻¹(S)`. "`A` supported outside the reduced boundary" is read as: no component of
`A` lies in `⌊B⌋`; `ord_F(A)` is the coefficient at `F` of the pull-back
`MMP.Mori.QDivisor.IsPullback`. The source works over `ℂ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

open MMP.Resolution TopologicalSpace

section LocalEquations

open scoped Classical in
/-- At a point `x` whose local ring is regular, a prime divisor `Γ ∋ x` has a nonzero local
equation `π`: the stalk of the ideal of `Γ` at `x` is `(π)`, and `ord_{Γ'} π` is `1` if `Γ' = Γ`
and `0` for every other prime divisor `Γ' ∋ x`. -/
theorem PrimeDivisor.exists_localEquation_of_isRegularLocalRing
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (x : X) (hreg : IsRegularLocalRing (X.presheaf.stalk x)) (Γ : MMP.Mori.PrimeDivisor X)
    (hΓ : x ∈ Γ.support) :
    ∃ π : X.presheaf.stalk x, π ≠ 0 ∧
      Γ.idealSheaf.stalkIdeal x = Ideal.span {π} ∧
      ∀ Γ' : MMP.Mori.PrimeDivisor X, x ∈ Γ'.support →
        X.ord (algebraMap _ X.functionField π) Γ'.genericPoint = if Γ' = Γ then 1 else 0 := by
  have := IsRegularLocalRing.uniqueFactorizationMonoid (X.presheaf.stalk x)
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  have hsp : Γ.genericPoint ⤳ x := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support Γ hΓ
  set q := MMP.Intersection.primeOfSpecializes hsp with hq
  -- the prime of `η_Γ` has height one
  have hq1 : q.height = 1 := by
    let := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
    have := MMP.Intersection.isLocalization_stalkSpecializes hsp
    have e := IsLocalization.AtPrime.ringKrullDim_eq_height q (X.presheaf.stalk Γ.genericPoint)
    rw [ringKrullDim_stalk_eq_coheight, Γ.coheight_genericPoint] at e
    exact_mod_cast e.symm
  -- the stalk of the ideal of `Γ`
  set I := IdealSheafData.stalk Γ.idealSheaf x with hI
  have hxs : x ∈ Γ.idealSheaf.support := hΓ
  have hIp : I.IsPrime := by
    have := Γ.integral
    obtain ⟨y, hy⟩ : x ∈ Set.range Γ.idealSheaf.subschemeι := by
      rwa [Scheme.IdealSheafData.range_subschemeι]
    rw [hI, ← hy, ← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
    exact RingHom.ker_isPrime _
  have hI0 : I ≠ ⊥ := by
    intro h0
    have := Γ.isDiscreteValuationRing_localRing
    have hmap := MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes Γ.idealSheaf hsp
    rw [MMP.Resolution.Aux.stalk_idealSheaf_genericPoint, ← hI, h0, Ideal.map_bot] at hmap
    exact IsDiscreteValuationRing.not_a_field _ hmap
  have hIq : I ≤ q :=
    (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes Γ.idealSheaf hsp).mp
      (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' Γ)
  obtain ⟨π, hπI, hπ⟩ := hIp.exists_mem_prime_of_ne_bot hI0
  have hqπ : q = Ideal.span {π} := Ideal.eq_span_singleton_of_height_eq_one hq1 (hIq hπI) hπ
  have hIπ : I = Ideal.span {π} :=
    le_antisymm (hqπ ▸ hIq) ((Ideal.span_singleton_le_iff_mem _).mpr hπI)
  refine ⟨π, hπ.ne_zero, by rwa [Scheme.IdealSheafData.stalkIdeal_eq_stalk],
    fun Γ' hΓ' => ?_⟩
  have hsp' : Γ'.genericPoint ⤳ x :=
    MMP.Resolution.Aux.genericPoint_specializes_of_mem_support Γ' hΓ'
  rw [← MMP.Mori.algebraMap_stalkSpecializes hsp' π]
  have hπK : algebraMap Γ'.localRing X.functionField
      ((X.presheaf.stalkSpecializes hsp').hom π) ≠ 0 := by
    rw [MMP.Mori.algebraMap_stalkSpecializes hsp' π]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero)
  split_ifs with hΓΓ'
  · subst hΓΓ'
    have := Γ'.isDiscreteValuationRing_localRing
    let := (X.presheaf.stalkSpecializes hsp').hom.toAlgebra
    have := MMP.Intersection.isLocalization_stalkSpecializes hsp'
    have hmax : IsLocalRing.maximalIdeal Γ'.localRing =
        Ideal.span {(X.presheaf.stalkSpecializes hsp').hom π} := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q (X.presheaf.stalk Γ'.genericPoint),
        hqπ, Ideal.map_span, Set.image_singleton]
      rfl
    have hirr : Irreducible ((X.presheaf.stalkSpecializes hsp').hom π) :=
      IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
        (fun h => by rw [h, map_zero] at hπK; exact hπK rfl) hmax
    rw [Scheme.ord_eq_iff Γ'.coheight_genericPoint hπK]
    have : Ring.KrullDimLE 1 Γ'.localRing :=
      krullDimLE_of_coheight_le Γ'.coheight_genericPoint.le
    exact Ring.ordFrac_irreducible hirr
  · refine Γ'.ord_algebraMap_of_isUnit ?_
    by_contra hnu
    have hmem : π ∈ MMP.Intersection.primeOfSpecializes hsp' := by
      change (X.presheaf.stalkSpecializes hsp').hom π ∈ IsLocalRing.maximalIdeal _
      exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hle : q ≤ MMP.Intersection.primeOfSpecializes hsp' := by
      rwa [hqπ, Ideal.span_singleton_le_iff_mem]
    have h1 := MMP.Intersection.specializes_of_primeOfSpecializes_le hsp hsp' hle
    apply hΓΓ'
    by_contra hne
    have hle : Γ'.genericPoint ≤ Γ.genericPoint := h1
    have hlt : Γ'.genericPoint < Γ.genericPoint := lt_of_le_not_ge hle fun h =>
      hne (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (Specializes.antisymm (show Γ'.genericPoint ⤳ Γ.genericPoint from h) h1).eq)
    have h2 := Order.coheight_add_one_le hlt
    rw [Γ.coheight_genericPoint, Γ'.coheight_genericPoint] at h2
    exact absurd h2 (by decide)

/-- The pull-back of a `ℚ`-Cartier divisor has coefficient zero along a prime divisor whose
generic point lies off the support. -/
theorem QDivisor.IsPullback.coeff_eq_zero_of_notMem {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {p : Y ⟶ X} {A : QDivisor X}
    (hAq : A.IsQCartier)
    {hA : ∀ Z : irreducibleComponents Y, p (componentGenericPoint Y Z) ∉ A.supp}
    {A' : QDivisor Y} (h : QDivisor.IsPullback p A hA A') (F : Mori.PrimeDivisor Y)
    (hF : p F.genericPoint ∉ (A.supp : Set X)) : A'.coeff F = 0 := by
  obtain ⟨m, hm, M, hM, hMc⟩ := hAq.exists_pos
  obtain ⟨D', hD', hpb⟩ := h m hm M hM hMc
  have hm' : ((m : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hMsupp : M.supp = A.supp :=
    QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hM
  set V : X.Opens := ⟨(M.supp : Set X)ᶜ, M.supp.isClosed.isOpen_compl⟩ with hV
  have hE : (F.support ∩ p ⁻¹ᵁ V).Nonempty := by
    refine (F.genericPoint_mem_iff _).mp ?_
    change p F.genericPoint ∉ (M.supp : Set X)
    rwa [hMsupp]
  have h0 : ∀ P : Mori.PrimeDivisor X, (P.support ∩ V).Nonempty → M.coeff P = 0 := by
    rintro P ⟨x, hxP, hxV⟩
    by_contra hne
    exact hxV (DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, hne, hxP⟩)
  have hge := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hMc (V := V)
    (fun P hP => (h0 P hP).ge) hpb F hE
  have hBn : ∀ Z : irreducibleComponents Y, p (componentGenericPoint Y Z) ∉ ((-1 : ℤ) • M).supp :=
    fun Z hZ => by
      obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
      rw [DivisorWithCoeffs.coeff_smul] at hP
      refine hA Z ?_
      rw [← hMsupp]
      exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, fun h => hP (by rw [h, smul_zero]), hxP⟩
  have hpbn := hpb.zsmul hMc (-1) hBn
  have hle := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (hMc.zsmul (-1)) (V := V)
    (fun P hP => by rw [DivisorWithCoeffs.coeff_smul, h0 P hP, smul_zero]) hpbn F hE
  rw [DivisorWithCoeffs.coeff_smul] at hle
  have hD0 : D'.coeff F = 0 := by
    have : (-1 : ℤ) • D'.coeff F = -D'.coeff F := by simp
    omega
  have h1 := congrArg (fun A => DivisorWithCoeffs.coeff A F) hD'
  simp only [Divisor.coeff_toQDivisor, hD0, Int.cast_zero, DivisorWithCoeffs.coeff_smul,
    zsmul_eq_mul] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_left hm'

end LocalEquations

end MMP.Mori

namespace MMP.Fourfold.ZeroPlaceExtraction

open MMP MMP.Mori MMP.Resolution MMP.Fourfold

open TopologicalSpace
open scoped WithZero

/-! ### The snc lower bound for discrepancies at the centre -/

section LowerBound

/-- A scheme separated over a field is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hsX : IsSeparated sX) : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- A divisor over a normal variety is exceptional if and only if its center has codimension at
least two. -/
private theorem isExceptional_iff_two_le_coheight {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := isSeparated_toTerminal hX.1.toIsSeparated
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- **Alternating maps on logarithmic vectors.** If the vectors `v_i`, `i ∈ T`, lie in
`ϖ M + R t` for a fixed `t ∈ M`, then `φ(v) ∈ ϖ^{|T| - 1} N`; if moreover some `v_{i₀}`, `i₀ ∉ T`,
equals `t`, then `φ(v) ∈ ϖ^{|T|} N`. -/
private theorem exists_eq_pow_smul_of_mem {R M N ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (φ : M [⋀^ι]→ₗ[R] N) (ϖ : R)
    (t : M) (T : Finset ι) :
    ∀ v : ι → M, (∀ i ∈ T, ∃ (a : M) (b : R), v i = ϖ • a + b • t) →
      (∃ η, φ v = ϖ ^ (T.card - 1) • η) ∧
        ((∃ i₀ ∉ T, v i₀ = t) → ∃ η, φ v = ϖ ^ T.card • η) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro v _
    exact ⟨⟨φ v, by simp⟩, fun _ => ⟨φ v, by simp⟩⟩
  | insert i T hiT ih =>
    intro v hv
    obtain ⟨a, b, hvi⟩ := hv i (Finset.mem_insert_self i T)
    have hsplit : φ v = ϖ • φ (Function.update v i a) + b • φ (Function.update v i t) := by
      conv_lhs => rw [← Function.update_eq_self i v, hvi]
      rw [AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
        AlternatingMap.map_update_smul]
    have hT : ∀ w : M, ∀ j ∈ T, ∃ (a : M) (b : R), Function.update v i w j = ϖ • a + b • t := by
      intro w j hj
      have hji : j ≠ i := fun h => hiT (h ▸ hj)
      rw [Function.update_of_ne hji]
      exact hv j (Finset.mem_insert_of_mem hj)
    have hcard := Finset.card_insert_of_notMem hiT
    obtain ⟨⟨η₁, h₁⟩, -⟩ := ih (Function.update v i a) (hT a)
    obtain ⟨-, h₂⟩ := ih (Function.update v i t) (hT t)
    obtain ⟨η₂, h₂⟩ := h₂ ⟨i, hiT, by simp⟩
    refine ⟨?_, ?_⟩
    · rw [hcard, Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos T.card with h0 | hpos
      · exact ⟨φ v, by rw [h0, pow_zero, one_smul]⟩
      · rw [hsplit, h₁, h₂]
        refine ⟨η₁ + b • η₂, ?_⟩
        rw [smul_smul, ← pow_succ', Nat.sub_add_cancel hpos, smul_add, smul_comm b]
    · rintro ⟨i₀, hi₀, hvi₀⟩
      have hi₀i : i₀ ≠ i := fun h => hi₀ (h ▸ Finset.mem_insert_self i T)
      have hi₀T : i₀ ∉ T := fun h => hi₀ (Finset.mem_insert_of_mem h)
      have hz : φ (Function.update v i t) = 0 :=
        AlternatingMap.map_eq_zero_of_eq φ _ (i := i) (j := i₀)
          (by rw [Function.update_self, Function.update_of_ne hi₀i, hvi₀]) hi₀i.symm
      obtain ⟨-, h₃⟩ := ih (Function.update v i a) (hT a)
      obtain ⟨η₃, h₃⟩ := h₃ ⟨i₀, hi₀T, by rw [Function.update_of_ne hi₀i, hvi₀]⟩
      refine ⟨η₃, ?_⟩
      rw [hsplit, hz, smul_zero, add_zero, h₃, smul_smul, ← pow_succ', hcard]

open scoped TensorProduct in
/-- **Regular parameters are part of a basis of the differentials.** On an integral scheme `X`
of dimension `n` smooth over a perfect field, a regular system of parameters
`z_1, …, z_c` of `𝒪_{X,x}` extends to a basis `dz_1, …, dz_c, w_{c+1}, …, w_n` of
`Ω_{𝒪_{X,x}/k}`; its wedge generates `Ω^n_{𝒪_{X,x}/k}` and has nonzero image in `Ω^n_{k(X)/k}`. -/
private theorem exists_topForms_generator_ιMulti {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] (sX : X ⟶ Spec (.of k)) [Smooth sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (x : X) {c : ℕ} {z : Fin c → X.presheaf.stalk x}
    (hz : IsRegularSystemOfParameters z) :
    letI := stalkAlgebra sX x
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX x
    ∃ (hcn : c ≤ n) (w : Fin n → Ω[X.presheaf.stalk x⁄k]),
      (∀ i : Fin c, w (Fin.castLE hcn i) = KaehlerDifferential.D k _ (z i)) ∧
      Submodule.span (X.presheaf.stalk x) {exteriorPower.ιMulti (X.presheaf.stalk x) n w} = ⊤ ∧
      topFormsMap k (X.presheaf.stalk x) X.functionField n
        (exteriorPower.ιMulti (X.presheaf.stalk x) n w) ≠ 0 := by
  classical
  let := stalkAlgebra sX x
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX x
  obtain ⟨h1, h2, h3⟩ := MMP.Flips.ResolutionInputs.stalk_facts sX x
  have := h1
  have := h2
  have := h3
  have : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    Algebra.EssFiniteType.of_surjective
      (IsScalarTower.toAlgHom k (X.presheaf.stalk x)
        (IsLocalRing.ResidueField (X.presheaf.stalk x))) IsLocalRing.residue_surjective
  have : Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    Algebra.FormallySmooth.of_perfectField
  obtain ⟨ht0, hli, -⟩ := MMP.Flips.ResolutionInputs.cotangent_basis_of_regular z hz.1 hz.2
  have hli' := MMP.Flips.ResolutionInputs.linearIndependent_tmul_D k z ht0 hli
  have : Module.Projective (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] :=
    ((Algebra.formallySmooth_iff _ _).mp ‹_›).1
  obtain ⟨e, v, hvS, hvli, hvsp⟩ := MMP.Flips.ResolutionInputs.exists_sumElim_basis _ hli' _
    (MMP.Flips.ResolutionInputs.span_tmul_range_D k)
  choose r hr using hvS
  have hu : (TensorProduct.mk (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x))
      Ω[X.presheaf.stalk x⁄k] 1 ∘ fun i => KaehlerDifferential.D k (X.presheaf.stalk x)
        (Sum.elim z r i)) = Sum.elim (fun i => (1 : IsLocalRing.ResidueField (X.presheaf.stalk x))
          ⊗ₜ KaehlerDifferential.D k (X.presheaf.stalk x) (z i)) v := by
    funext i
    cases i with
    | inl i => rfl
    | inr j => exact hr j
  have hbij : Function.Bijective (Finsupp.linearCombination (X.presheaf.stalk x)
      (fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (Sum.elim z r i))) := by
    apply Module.IsLocalRing.linearCombination_bijective_of_flat
    rw [hu]
    refine ⟨hvli, ?_⟩
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact top_le_iff.mp hvsp
  let B := MMP.Flips.ResolutionInputs.basisOfBijective _ hbij
  have hB : ∀ i, B i = KaehlerDifferential.D k (X.presheaf.stalk x) (Sum.elim z r i) :=
    MMP.Flips.ResolutionInputs.basisOfBijective_apply _ hbij
  -- the rank of the differentials is `n`
  obtain ⟨n', ⟨b⟩, hn'⟩ := MMP.Threefold.Resolution.exists_basis_kaehler_stalk sX x
  have hnn' : n' = n := by
    have := (topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X sX x).trans hn'
    rw [hn] at this
    exact_mod_cast this.symm
  have hce : c + e = n := by
    have := Module.Basis.indexEquiv b B
    have h := Fintype.card_congr this
    rw [Fintype.card_fin, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
    omega
  let b' : Module.Basis (Fin n) (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] :=
    B.reindex (finSumFinEquiv.trans (finCongr hce))
  have hcn : c ≤ n := by omega
  refine ⟨hcn, b', fun i => ?_, ?_, ?_⟩
  · simp only [b', Module.Basis.reindex_apply, Equiv.symm_trans_apply, finCongr_symm,
      finCongr_apply]
    have : Fin.cast hce.symm (Fin.castLE hcn i) = Fin.castAdd e i := Fin.ext rfl
    rw [this, finSumFinEquiv_symm_apply_castAdd, hB]
    rfl
  · rw [eq_top_iff]
    intro ω _
    obtain ⟨t, ht⟩ := (MMP.Intersection.bijective_smul_ιMulti_basis b').2 ω
    rw [← ht]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · have := MMP.Threefold.Resolution.nontrivial_topForms sX hn
    refine topFormsMap_ne_zero_of_span_eq_top ?_
    rw [eq_top_iff]
    intro ω _
    obtain ⟨t, ht⟩ := (MMP.Intersection.bijective_smul_ιMulti_basis b').2 ω
    rw [← ht]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- `d(u ϖ^e) = ϖ^{e-1}(ϖ du + e u dϖ)` for `e ≥ 1`. -/
private theorem D_mul_pow {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] (u ϖ : R)
    {e : ℕ} (he : 1 ≤ e) :
    KaehlerDifferential.D k R (u * ϖ ^ e) = ϖ ^ (e - 1) •
      (ϖ • KaehlerDifferential.D k R u + ((e : R) * u) • KaehlerDifferential.D k R ϖ) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [Derivation.leibniz, Derivation.leibniz_pow]
  simp only [add_tsub_cancel_left]
  rw [pow_add, pow_one, ← Nat.cast_smul_eq_nsmul R]
  module

/-- **Logarithmic poles are simple.** Let `R` be a discrete valuation ring with uniformizer `ϖ`
over a field `k`, and `σ` a generator of `Ω^n_{R/k}` with nonzero image in `Ω^n_{K/k}`. If
`h σ = dg_1 ∧ ⋯ ∧ dg_c ∧ v_{c+1} ∧ ⋯ ∧ v_n` with `c ≥ 1` and `g_i = u_i ϖ^{e_i}`, `u_i` units
and `e_i ≥ 1`, then `h ∈ 𝔪^{e_1 + ⋯ + e_c - 1}`: writing `dg_i = g_i dlog g_i`, the wedge of the
logarithmic forms `dlog g_i ∈ Ω_R + R dϖ/ϖ` has at most a simple pole. -/
private theorem mem_maximalIdeal_pow_of_ιMulti_eq_smul {k R K : Type*} [Field k] [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R] [Field K] [Algebra k K] [Algebra R K]
    [IsScalarTower k R K] [IsFractionRing R K] {n c : ℕ} (hcn : c ≤ n) (hc : 1 ≤ c) {ϖ : R}
    (hϖ : Irreducible ϖ) {σ : ⋀[R]^n Ω[R⁄k]} (hσ : Submodule.span R {σ} = ⊤)
    (h0 : topFormsMap k R K n σ ≠ 0) (v : Fin n → Ω[R⁄k]) (u : Fin c → Rˣ) (e : Fin c → ℕ)
    (he : ∀ i, 1 ≤ e i)
    (hv : ∀ i : Fin c, v (Fin.castLE hcn i) = KaehlerDifferential.D k R (u i * ϖ ^ e i))
    {h : R} (hh : exteriorPower.ιMulti R n v = h • σ) :
    h ∈ IsLocalRing.maximalIdeal R ^ (∑ i, e i - 1) := by
  classical
  -- the data indexed by `Fin n`
  let ee : Fin n → ℕ := fun i => if hi : (i : ℕ) < c then e ⟨i, hi⟩ else 0
  let uu : Fin n → R := fun i => if hi : (i : ℕ) < c then (u ⟨i, hi⟩ : R) else 1
  let w : Fin n → Ω[R⁄k] := fun i => if (i : ℕ) < c then
    ϖ • KaehlerDifferential.D k R (uu i) + ((ee i : R) * uu i) • KaehlerDifferential.D k R ϖ
    else v i
  have hvw : v = fun i => ϖ ^ (ee i - 1) • w i := by
    funext i
    by_cases hi : (i : ℕ) < c
    · have := hv ⟨i, hi⟩
      simp only [Fin.castLE_mk] at this
      simp only [w, ee, uu, dite_eq_left hi, ite_eq_left hi]
      rw [this]
      exact D_mul_pow _ _ (he _)
    · simp [w, ee, hi]
  set T : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb hcn) with hT
  have hTc : T.card = c := by simp [hT]
  have hwT : ∀ i ∈ T, ∃ (a : Ω[R⁄k]) (b : R), w i = ϖ • a + b • KaehlerDifferential.D k R ϖ := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
    have hj : ((Fin.castLEEmb hcn j : Fin n) : ℕ) < c := j.2
    refine ⟨KaehlerDifferential.D k R (uu (Fin.castLEEmb hcn j)),
      (ee (Fin.castLEEmb hcn j) : R) * uu (Fin.castLEEmb hcn j), ?_⟩
    simp only [w, ite_eq_left hj]
  obtain ⟨⟨η, hη⟩, -⟩ := exists_eq_pow_smul_of_mem (M := Ω[R⁄k]) (N := ⋀[R]^n Ω[R⁄k])
    (exteriorPower.ιMulti R n) ϖ (KaehlerDifferential.D k R ϖ) T w hwT
  have hprod : exteriorPower.ιMulti R n v = ϖ ^ (∑ i, (ee i - 1)) • exteriorPower.ιMulti R n w := by
    rw [hvw, AlternatingMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hσ ▸ Submodule.mem_top : η ∈ _)
  -- the exponent
  have hsum : ∑ i, (ee i - 1) + (c - 1) = ∑ i, e i - 1 := by
    have h1 : ∑ i : Fin n, (ee i - 1) = ∑ i : Fin c, (e i - 1) := by
      rw [← Finset.sum_subset (Finset.subset_univ T) fun i _ hiT => ?_]
      · rw [hT, Finset.sum_map]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : ((Fin.castLEEmb hcn j : Fin n) : ℕ) < c := j.2
        simp only [ee, dite_eq_left hj]
        rfl
      · have hi : ¬ (i : ℕ) < c := fun hi =>
          hiT (Finset.mem_map.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        simp [ee, hi]
    have h2 : ∑ i : Fin c, (e i - 1) + c = ∑ i, e i := by
      have : ∑ i : Fin c, e i = ∑ i : Fin c, ((e i - 1) + 1) :=
        Finset.sum_congr rfl fun i _ => (Nat.sub_add_cancel (he i)).symm
      rw [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one]
    omega
  have hrel : h • σ = (ϖ ^ (∑ i, e i - 1) * r) • σ := by
    rw [← hh, hprod, hη, hTc, ← hr, smul_smul, smul_smul, ← pow_add, hsum]
  -- cancel `σ` in `Ω^n_{K/k}`
  have hK : algebraMap R K h = algebraMap R K (ϖ ^ (∑ i, e i - 1) * r) := by
    have := congrArg (topFormsMap k R K n) hrel
    rw [LinearMap.map_smul (topFormsMap k R K n) h σ,
      LinearMap.map_smul (topFormsMap k R K n) (ϖ ^ (∑ i, e i - 1) * r) σ,
      ← algebraMap_smul K h (topFormsMap k R K n σ),
      ← algebraMap_smul K (ϖ ^ (∑ i, e i - 1) * r) (topFormsMap k R K n σ)] at this
    have h' := sub_eq_zero.mpr this
    rw [← sub_smul, smul_eq_zero] at h'
    exact sub_eq_zero.mp (h'.resolve_right h0)
  rw [IsFractionRing.injective R K hK]
  refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ _)
  exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit

/-- Along a prime divisor `F` with uniformizer `ϖ`, the order of `u ϖ^m`, `u` a unit, is `m`. -/
private theorem ord_unit_mul_pow {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (F : MMP.Mori.PrimeDivisor Y) [IsDiscreteValuationRing F.localRing] {ϖ : F.localRing}
    (hϖ : Irreducible ϖ) (v : F.localRingˣ) (m : ℕ) :
    Y.ord (algebraMap F.localRing Y.functionField (v * ϖ ^ m)) F.genericPoint = m := by
  have hϖK : algebraMap F.localRing Y.functionField ϖ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero
      hϖ.ne_zero)
  have hord1 : Y.ord (algebraMap F.localRing Y.functionField ϖ) F.genericPoint = 1 := by
    rw [Scheme.ord_eq_iff F.coheight_genericPoint hϖK]
    have : Ring.KrullDimLE 1 F.localRing := krullDimLE_of_coheight_le F.coheight_genericPoint.le
    exact Ring.ordFrac_irreducible hϖ
  have hvK : algebraMap F.localRing Y.functionField v ≠ 0 := (v.isUnit.map _).ne_zero
  rw [map_mul, Scheme.ord_mul hvK (by rw [map_pow]; exact pow_ne_zero _ hϖK),
    F.ord_algebraMap_of_isUnit v.isUnit, map_pow, ← zpow_natCast,
    MMP.Mori.ord_zpow _ hϖK, hord1]
  simp

/-- Along a prime divisor `F` with uniformizer `ϖ`, a nonzero element of `𝔪_F^N` has order at
least `N`. -/
private theorem le_ord_of_mem_pow {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (F : MMP.Mori.PrimeDivisor Y) [IsDiscreteValuationRing F.localRing] {h : F.localRing}
    (hh : h ≠ 0) {N : ℕ} (hN : h ∈ IsLocalRing.maximalIdeal F.localRing ^ N) :
    (N : ℤ) ≤ Y.ord (algebraMap F.localRing Y.functionField h) F.genericPoint := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible F.localRing
  obtain ⟨M, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hh hϖ
  rw [ord_unit_mul_pow F hϖ v M, Nat.cast_le]
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    Units.dvd_mul_left] at hN
  exact (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp hN

/-- **The pull-back of a top form along a birational morphism is nonzero at a prime divisor.**
If `f : Y ⟶ X` is dominant with `f^* : k(X) ≅ k(Y)`, a top form `σ` at `f(η_F)` with nonzero
image in `Ω^d_{k(X)/k}` has nonzero image in `Ω^d_{𝒪_{Y,F}/k}`. -/
private theorem topFormsMap_stalk_localRing_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (F : MMP.Mori.PrimeDivisor Y)
    {σA : letI := stalkAlgebra sX (f F.genericPoint)
      ⋀[X.presheaf.stalk (f F.genericPoint)]^d Ω[X.presheaf.stalk (f F.genericPoint)⁄k]}
    (h0A : letI := stalkAlgebra sX (f F.genericPoint)
      letI := functionFieldAlgebra sX
      haveI := isScalarTower_stalk_functionField sX (f F.genericPoint)
      topFormsMap k (X.presheaf.stalk (f F.genericPoint)) X.functionField d σA ≠ 0) :
    letI := stalkAlgebra sX (f F.genericPoint)
    letI := stalkAlgebra (f ≫ sX) F.genericPoint
    letI := (f.stalkMap F.genericPoint).hom.toAlgebra
    haveI := MMP.Threefold.Resolution.isScalarTower_stalkMap sX f F.genericPoint
    topFormsMap k (X.presheaf.stalk (f F.genericPoint)) F.localRing d σA ≠ 0 := by
  let := stalkAlgebra sX (f F.genericPoint)
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX (f F.genericPoint)
  let := stalkAlgebra (f ≫ sX) F.genericPoint
  let := functionFieldAlgebra (f ≫ sX)
  have := isScalarTower_stalk_functionField (f ≫ sX) F.genericPoint
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  let := (f.stalkMap F.genericPoint).hom.toAlgebra
  have := MMP.Threefold.Resolution.isScalarTower_stalkMap sX f F.genericPoint
  let : Algebra (X.presheaf.stalk (f F.genericPoint)) Y.functionField :=
    ((algebraMap X.functionField Y.functionField).comp
      (algebraMap (X.presheaf.stalk (f F.genericPoint)) X.functionField)).toAlgebra
  have : IsScalarTower (X.presheaf.stalk (f F.genericPoint)) X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (X.presheaf.stalk (f F.genericPoint)) F.localRing Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      MMP.Mori.functionFieldMap_algebraMap_stalk f F.genericPoint a
  have : IsScalarTower k (X.presheaf.stalk (f F.genericPoint)) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k X.functionField Y.functionField,
        IsScalarTower.algebraMap_apply k (X.presheaf.stalk (f F.genericPoint)) X.functionField]
      rfl
  intro h0
  have e1 := MMP.Threefold.Mori.Helpers.topFormsMap_comp (k := k) (A := X.presheaf.stalk
    (f F.genericPoint)) (B := F.localRing) (C := Y.functionField) (d := d) σA
  have e2 := MMP.Threefold.Mori.Helpers.topFormsMap_comp (k := k) (A := X.presheaf.stalk
    (f F.genericPoint)) (B := X.functionField) (C := Y.functionField) (d := d) σA
  rw [h0, map_zero, ← e2] at e1
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (hω₀.1 ▸ Submodule.mem_top : topFormsMap k (X.presheaf.stalk (f F.genericPoint))
      X.functionField d σA ∈ _)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    exact h0A ht.symm
  rw [← ht, map_smul, ← algebraMap_smul Y.functionField t] at e1
  exact smul_ne_zero ((map_ne_zero _).mpr ht0) hω₀.2.2 e1.symm

open scoped Classical in
/-- **The lower bound for one exceptional divisor.** Let `(Y, f, E)` be exceptional over a smooth
variety `X`, with center `x₀ = f(η_E)` of codimension `c ≥ 2`, and let `T` be the components of
the snc divisor `∑_{G ∈ S} G` through `x₀`. Then
`a(E, X, Δ) ≥ -1 + ∑_{G ∈ T} (1 - a_G) + (c - |T|)`.

In a regular system of parameters `z_1, …, z_c` of `𝒪_{X,x₀}` containing local equations of
the `G ∈ T`, the form `σ = dz_1 ∧ ⋯ ∧ dz_c ∧ w` generates `ω_{X,x₀}`, and a local generator of
`𝒪_X(m(K_X + Δ))` at `x₀` is `σ^{⊗m} ∏_{G ∈ T} z_G^{-m a_G}` up to a unit. Along `E`,
`σ = ∏ z_i · (dlog z_1 ∧ ⋯ ∧ dlog z_c ∧ w)` has order at least `∑ e_i - 1`, `e_i = ord_E z_i ≥ 1`,
since a wedge of logarithmic forms has at most a simple pole. -/
private theorem le_isDiscrepancy_of_isSNC {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {Δ : QDivisor X} {S : Finset (MMP.Mori.PrimeDivisor X)}
    (hS : Δ.support ⊆ S) (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    (hcoeff : ∀ E ∈ S, Δ.coeff E ≤ 1) (D : DivisorOver k sX) (hD : D.IsExceptional) {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) :
    ∃ c : ℕ, Order.coheight (D.f D.E.genericPoint) = c ∧ 2 ≤ c ∧
      (S.filter (fun G => D.f D.E.genericPoint ∈ G.support)).card ≤ c ∧
      -1 + ∑ G ∈ S.filter (fun G => D.f D.E.genericPoint ∈ G.support), (1 - Δ.coeff G) +
        ((c : ℚ) - (S.filter (fun G => D.f D.E.genericPoint ∈ G.support)).card) ≤ a := by
  classical
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : Smooth sX := (isSmoothScheme_iff sX).mp hsm
  have hn := hK.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have hbij : Function.Bijective (functionFieldMap D.f) :=
    D.isBirationalMorphism.functionFieldMap_bijective
  have : LocallyOfFiniteType (D.f ≫ sX) := D.isNormalVariety.1.toLocallyOfFiniteType
  have hdY : (letI := functionFieldAlgebra (D.f ≫ sX)
      (Algebra.trdeg k D.Y.functionField).toNat = n) := by
    rwa [← trdeg_functionField_eq_of_bijective sX D.f hbij]
  have hcod : 2 ≤ Order.coheight (D.f D.E.genericPoint) :=
    (isExceptional_iff_two_le_coheight hX D).mp hD
  have hreg := isRegularLocalRing_stalk_of_smooth_over_field sX (D.f D.E.genericPoint)
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk (D.f D.E.genericPoint))
  obtain ⟨c, z, j, hz, hj, hI⟩ := exists_at_of_isSNC hsnc (D.f D.E.genericPoint)
  have hc2 : 2 ≤ c := by
    rw [coheight_eq_of_isRegularSystemOfParameters hz] at hcod
    exact_mod_cast hcod
  set T := S.filter (fun G => D.f D.E.genericPoint ∈ G.support) with hT
  have hTmem : ∀ G ∈ T, G ∈ S ∧ D.f D.E.genericPoint ∈ G.support :=
    fun G hG => Finset.mem_filter.mp hG
  let jT : MMP.Mori.PrimeDivisor X → Fin c := fun G =>
    if h : G ∈ S ∧ D.f D.E.genericPoint ∈ G.support then j ⟨G, h⟩ else ⟨0, by omega⟩
  have hjT : ∀ G (h : G ∈ T), jT G = j ⟨G, hTmem G h⟩ := fun G h => dite_eq_left _
  have hinj : Set.InjOn jT T := fun G hG G' hG' h => by
    rw [hjT G hG, hjT G' hG'] at h
    exact congrArg Subtype.val (hj h)
  have hcard : T.card ≤ c := by
    have := Finset.card_le_card_of_injOn jT (t := Finset.univ) (fun _ _ => Finset.mem_univ _) hinj
    simpa using this
  refine ⟨c, coheight_eq_of_isRegularSystemOfParameters hz, hc2, hcard, ?_⟩
  -- the discrepancy data
  obtain ⟨-, -, m, hm, -, U, hU, τ, hτ, hτa⟩ := ha
  -- a generator `σ_A = dz_1 ∧ ⋯ ∧ dz_c ∧ w` at `x₀`
  obtain ⟨hcn, w, hw, hσA, h0A⟩ :=
    exists_topForms_generator_ιMulti sX hn (D.f D.E.genericPoint) hz
  let := stalkAlgebra sX (D.f D.E.genericPoint)
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX (D.f D.E.genericPoint)
  let := stalkAlgebra (D.f ≫ sX) D.E.genericPoint
  let := functionFieldAlgebra (D.f ≫ sX)
  have := isScalarTower_stalk_functionField (D.f ≫ sX) D.E.genericPoint
  let := (D.f.stalkMap D.E.genericPoint).hom.toAlgebra
  have := MMP.Threefold.Resolution.isScalarTower_stalkMap sX D.f D.E.genericPoint
  have := D.E.isDiscreteValuationRing_localRing
  -- a generator `σ_B` at `η_E`, and `f^♯ σ_A = h' σ_B`
  obtain ⟨σB, hσB, h0B⟩ := D.E.exists_topForms_generator (sX := D.f ≫ sX) hdY
  obtain ⟨h', hrel⟩ : ∃ h' : D.E.localRing,
      topFormsMap k (X.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing n
        (exteriorPower.ιMulti (X.presheaf.stalk (D.f D.E.genericPoint)) n w) = h' • σB := by
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hσB ▸ Submodule.mem_top :
      topFormsMap k (X.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing n
        (exteriorPower.ιMulti (X.presheaf.stalk (D.f D.E.genericPoint)) n w) ∈ _)
    exact ⟨t, ht.symm⟩
  have hne := topFormsMap_stalk_localRing_ne_zero sX D.f hbij hd D.E h0A
  have hh'0 : h' ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hrel
    exact hne hrel
  have hh : algebraMap D.E.localRing D.Y.functionField h' ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hh'0)
  have hord := MMP.Threefold.Resolution.ordForm_pullbackRationalPluriForms_eq sX D.f D.E hσA h0A
    hσB h0B h' hrel hh hτ.1
  -- the parameters along `E`: `f^♯ z_i = u_i ϖ^{e_i}` with `e_i ≥ 1`
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D.E.localRing
  have hzm : ∀ i, z i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (D.f D.E.genericPoint)) :=
    fun i => hz.1 ▸ Ideal.subset_span ⟨i, rfl⟩
  have hz0 : ∀ i, (D.f.stalkMap D.E.genericPoint).hom (z i) ≠ 0 := by
    intro i h0
    have hzi : z i ≠ 0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz i
    have := MMP.Mori.functionFieldMap_algebraMap_stalk D.f D.E.genericPoint (z i)
    rw [h0, map_zero] at this
    exact (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hzi)) this
  have hzmE : ∀ i, (D.f.stalkMap D.E.genericPoint).hom (z i) ∈
      IsLocalRing.maximalIdeal D.E.localRing := fun i =>
    (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp (hzm i) (isUnit_of_map_unit _ _ hu)
  choose e u hzu using fun i =>
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hz0 i) hϖ
  have he : ∀ i, 1 ≤ e i := by
    intro i
    by_contra h0
    have h0 : e i = 0 := by omega
    have := hzmE i
    rw [hzu i, h0, pow_zero, mul_one] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp this (u i).isUnit
  have hordz : ∀ i, D.Y.ord (algebraMap D.E.localRing D.Y.functionField
      ((D.f.stalkMap D.E.genericPoint).hom (z i))) D.E.genericPoint = e i := by
    intro i
    rw [hzu i]
    exact ord_unit_mul_pow D.E hϖ (u i) (e i)
  -- the logarithmic estimate: `ord_E h' ≥ ∑ e_i - 1`
  have hvi : ∀ i : Fin c, KaehlerDifferential.map k k (X.presheaf.stalk (D.f D.E.genericPoint))
      D.E.localRing (w (Fin.castLE hcn i)) =
        KaehlerDifferential.D k D.E.localRing (u i * ϖ ^ e i) := by
    intro i
    rw [hw i, KaehlerDifferential.map_D, ← hzu i]
    rfl
  have hrel' : exteriorPower.ιMulti D.E.localRing n (fun i => KaehlerDifferential.map k k
      (X.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (w i)) = h' • σB := by
    rw [← topFormsMap_ιMulti]
    exact hrel
  have hmem := mem_maximalIdeal_pow_of_ιMulti_eq_smul (K := D.Y.functionField) hcn (by omega) hϖ
    hσB h0B _ u e he hvi hrel'
  have hordh := le_ord_of_mem_pow D.E hh'0 hmem
  -- the coefficient `g` of `τ` along `σ_A^{⊗m}`: `ord_Γ g = -m a_Γ` through `x₀`
  let g := formCoeff (k := k) (X.presheaf.stalk (D.f D.E.genericPoint)) hσA h0A
    (show PluriForms k X.functionField n m from τ)
  have hg0 : g ≠ 0 := fun h0 => hτ.1 ((formCoeff_eq_zero_iff hσA h0A _).mp h0)
  have hgΓ : ∀ Γ : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support →
      (X.ord g Γ.genericPoint : ℝ) = -((m : ℝ) * (Δ.coeff Γ : ℝ)) := by
    intro Γ hΓ
    have e1 := MMP.Threefold.Resolution.ordForm_eq_ord_formCoeff sX (D.f D.E.genericPoint) Γ hΓ
      hσA h0A τ
    have e2 := hτ.2 Γ ⟨_, hΓ, hU⟩
    rw [e1] at e2
    have := congrArg (fun q : ℚ => (q : ℝ)) e2
    push_cast at this
    linarith
  -- local equations of the components through `x₀`
  have hπex : ∀ G : T, ∃ π : X.presheaf.stalk (D.f D.E.genericPoint), π ≠ 0 ∧
      G.1.idealSheaf.stalkIdeal (D.f D.E.genericPoint) = Ideal.span {π} ∧
      ∀ Γ' : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ'.support →
        X.ord (algebraMap _ X.functionField π) Γ'.genericPoint = if Γ' = G.1 then 1 else 0 :=
    fun G =>
      PrimeDivisor.exists_localEquation_of_isRegularLocalRing _ hreg G.1 (hTmem G.1 G.2).2
  choose π hπ0 hπI hπord using hπex
  have hπE : ∀ G : T, D.Y.ord (functionFieldMap D.f (algebraMap _ X.functionField (π G)))
      D.E.genericPoint = e (jT G.1) := by
    intro G
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
    have hspan : Ideal.span {π G} = Ideal.span {z (jT G.1)} := by
      rw [hjT G.1 G.2, ← hI ⟨G.1, hTmem G.1 G.2⟩, ← Scheme.IdealSheafData.stalkIdeal_eq_stalk,
        hπI G]
    obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
    have hmul := congrArg (D.f.stalkMap D.E.genericPoint).hom hv
    rw [map_mul] at hmul
    have h1 : algebraMap D.E.localRing D.Y.functionField
        ((D.f.stalkMap D.E.genericPoint).hom (π G)) ≠ 0 := by
      refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero ?_)
      exact left_ne_zero_of_mul (hmul ▸ hz0 (jT G.1))
    have hvu : IsUnit ((D.f.stalkMap D.E.genericPoint).hom (v : X.presheaf.stalk _)) :=
      v.isUnit.map _
    have h2 := Scheme.ord_mul (X := D.Y) (x := D.E.genericPoint) h1
      (hvu.map (algebraMap D.E.localRing D.Y.functionField)).ne_zero
    rw [← map_mul, hmul, hordz, D.E.ord_algebraMap_of_isUnit hvu, add_zero] at h2
    exact h2.symm
  -- the Hartogs relation along `E`
  let Gf : Option T → X.functionField := fun i =>
    Option.elim i g fun G => algebraMap _ X.functionField (π G)
  let wt : Option T → ℝ := fun i => Option.elim i 1 fun G => (m : ℝ) * (Δ.coeff G.1 : ℝ)
  have hGf : ∀ i, Gf i ≠ 0 := by
    rintro (_ | G)
    · exact hg0
    · exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero (hπ0 G))
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := D.f) D.E Gf hGf wt
    fun Γ hΓ => by
      simp only [Fintype.sum_option, Gf, wt, Option.elim]
      rw [hgΓ Γ hΓ]
      simp_rw [hπord _ Γ hΓ]
      by_cases hΓT : Γ ∈ T
      · rw [Finset.sum_eq_single ⟨Γ, hΓT⟩]
        · simp
        · rintro G - hne
          have : Γ ≠ G.1 := fun h => hne (Subtype.ext h.symm)
          simp [this]
        · simp
      · have hΓS : Γ ∉ S := fun h => hΓT (Finset.mem_filter.mpr ⟨h, hΓ⟩)
        have h0 : Δ.coeff Γ = 0 := by
          rw [DivisorWithCoeffs.coeff_apply]
          exact Finsupp.notMem_support_iff.mp fun h => hΓS (hS h)
        rw [h0]
        simp only [Rat.cast_zero, mul_zero, neg_zero, mul_one, zero_add]
        refine Finset.sum_eq_zero fun G _ => ?_
        have : Γ ≠ G.1 := fun h => hΓT (h ▸ G.2)
        simp [this]
  simp only [Fintype.sum_option, Gf, wt, Option.elim, mul_one] at key
  simp_rw [hπE] at key
  push_cast at key
  -- the numerical conclusion
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmain : (m : ℝ) * (a : ℝ) = (D.Y.ord (functionFieldMap D.f g) D.E.genericPoint : ℝ) +
      (m : ℝ) * (D.Y.ord (algebraMap D.E.localRing D.Y.functionField h') D.E.genericPoint : ℝ) := by
    have h1 : (m : ℚ) * a = D.ordPullback τ := hτa
    have h2 : D.ordPullback τ = _ := hord
    rw [h2] at h1
    have := congrArg (fun q : ℚ => (q : ℝ)) h1
    push_cast at this
    exact this
  have hordh' : ((∑ i, e i - 1 : ℕ) : ℝ) ≤
      (D.Y.ord (algebraMap D.E.localRing D.Y.functionField h') D.E.genericPoint : ℝ) := by
    exact_mod_cast hordh
  have hsub : ((∑ i, e i - 1 : ℕ) : ℝ) = ((∑ i, e i : ℕ) : ℝ) - 1 := by
    have : 1 ≤ ∑ i, e i := by
      calc 1 ≤ e ⟨0, by omega⟩ := he _
        _ ≤ ∑ i, e i := Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
    push_cast [this]
    ring
  -- `a ≥ ∑ e_i - 1 - ∑_{G ∈ T} e_{j G} a_G`
  have hlow : ((∑ i, e i : ℕ) : ℝ) - 1 - ∑ G : T, (e (jT G.1) : ℝ) * (Δ.coeff G.1 : ℝ) ≤ a := by
    have h3 : (D.Y.ord (functionFieldMap D.f g) D.E.genericPoint : ℝ) =
        -∑ G : T, (e (jT G.1) : ℝ) * ((m : ℝ) * (Δ.coeff G.1 : ℝ)) := by
      linarith
    have h4 : ∑ G : T, (e (jT G.1) : ℝ) * ((m : ℝ) * (Δ.coeff G.1 : ℝ)) =
        (m : ℝ) * ∑ G : T, (e (jT G.1) : ℝ) * (Δ.coeff G.1 : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h4] at h3
    have h5 : (m : ℝ) * (((∑ i, e i : ℕ) : ℝ) - 1 - ∑ G : T, (e (jT G.1) : ℝ) *
        (Δ.coeff G.1 : ℝ)) ≤ (m : ℝ) * a := by
      rw [hmain, h3, ← hsub]
      nlinarith [hordh']
    exact le_of_mul_le_mul_left h5 hm'
  -- the combinatorial bound
  have hsplit : ((∑ i, e i : ℕ) : ℝ) = ∑ G ∈ T, (e (jT G) : ℝ) +
      ∑ i ∈ (T.image jT)ᶜ, (e i : ℝ) := by
    push_cast
    rw [← Finset.sum_add_sum_compl (T.image jT), Finset.sum_image hinj]
  have hcompl : ((c : ℝ) - T.card) ≤ ∑ i ∈ (T.image jT)ᶜ, (e i : ℝ) := by
    have hc' : ((T.image jT)ᶜ.card : ℝ) = c - T.card := by
      rw [Finset.card_compl, Fintype.card_fin, Finset.card_image_of_injOn hinj]
      push_cast [hcard]
      ring
    rw [← hc']
    have := Finset.card_nsmul_le_sum (T.image jT)ᶜ (fun i => (e i : ℝ)) 1
      (fun i _ => by exact_mod_cast he i)
    simpa using this
  have hterm : ∑ G ∈ T, (1 - (Δ.coeff G : ℝ)) ≤
      ∑ G ∈ T, (e (jT G) : ℝ) - ∑ G ∈ T, (e (jT G) : ℝ) * (Δ.coeff G : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun G hG => ?_
    have h1 : (Δ.coeff G : ℝ) ≤ 1 := by exact_mod_cast hcoeff G (hTmem G hG).1
    have h2 : (1 : ℝ) ≤ e (jT G) := by exact_mod_cast he (jT G)
    nlinarith
  have hTsum : ∑ G : T, (e (jT G.1) : ℝ) * (Δ.coeff G.1 : ℝ) =
      ∑ G ∈ T, (e (jT G) : ℝ) * (Δ.coeff G : ℝ) :=
    Finset.sum_coe_sort T (fun G => (e (jT G) : ℝ) * (Δ.coeff G : ℝ))
  rw [hTsum, hsplit] at hlow
  have hfin : ((-1 + ∑ G ∈ T, (1 - Δ.coeff G) + ((c : ℚ) - T.card) : ℚ) : ℝ) ≤ (a : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hfin

end LowerBound

/-! ### Zariski sequences blowing up the whole scheme -/

section Zariski

open IsLocalRing TopologicalSpace MMP.Mori.ZariskiSequence

variable {A : Type u} [CommRing A] [IsDomain A]

/-- The specialisation map of stalks into the generic point of an integral scheme is
injective. -/
private lemma stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y] {w z : Y}
    (hw : IsGenericPoint w Set.univ) (h : w ⤳ z) :
    Function.Injective (Y.presheaf.stalkSpecializes h) := by
  obtain rfl : w = genericPoint Y := hw.eq (genericPoint_spec Y)
  exact IsFractionRing.injective (Y.presheaf.stalk z) Y.functionField

private lemma stalkSpecializes_bijective_of_eq {Y : Scheme.{u}} {a b : Y} (hab : a = b)
    (h : a ⤳ b) : Function.Bijective (Y.presheaf.stalkSpecializes h) := by
  subst hab
  rw [show h = specializes_refl a from rfl, TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

/-- The image of the point of the spectrum of a field under an injective map is the generic
point. -/
private lemma Spec_map_apply_eq_genericPoint {K : Type u} [Field K] (φ : A →+* K)
    (hφ : Function.Injective φ) (q : Spec (.of K)) :
    Spec.map (CommRingCat.ofHom φ) q = genericPoint (Spec (.of A)) := by
  rw [genericPoint_eq_bot_of_affine]
  refine PrimeSpectrum.ext ?_
  change Ideal.comap φ q.asIdeal = ⊥
  haveI := q.isPrime
  rw [Ideal.eq_bot_of_prime q.asIdeal]
  exact Ideal.comap_bot_of_injective φ hφ

/-- If the stalk map at the generic point is surjective and `A` is not a field, the closed
point does not go to the generic point. -/
private lemma not_isGenericPoint_closedPoint [IsLocalRing A] {Y : Scheme.{u}}
    (g : Spec (.of A) ⟶ Y) (hA : ¬ IsField A)
    (ha : IsGenericPoint (g (genericPoint (Spec (.of A)))) Set.univ)
    (hb : Function.Surjective (g.stalkMap (genericPoint (Spec (.of A))))) :
    ¬ IsGenericPoint (g (closedPoint A)) Set.univ := by
  intro hy
  let y : Spec (.of A) := closedPoint A
  have hηy : genericPoint (Spec (.of A)) ⤳ y := (genericPoint_spec _).specializes trivial
  have hsurj : Function.Surjective ((Spec (.of A)).presheaf.stalkSpecializes hηy) := by
    intro t
    obtain ⟨s, rfl⟩ := hb t
    obtain ⟨s', rfl⟩ := (stalkSpecializes_bijective_of_eq (ha.eq hy)
      (g.base.hom.map_specializes hηy)).2 s
    exact ⟨g.stalkMap y s', (g.stalkSpecializes_stalkMap_apply _ _ hηy s').symm⟩
  have hinj := stalkSpecializes_injective (genericPoint_spec (Spec (.of A))) hηy
  let e₁ := RingEquiv.ofBijective ((Spec (.of A)).presheaf.stalkSpecializes hηy).hom ⟨hinj, hsurj⟩
  let e₂ := (stalkClosedPointIso (.of A)).commRingCatIsoToRingEquiv
  exact hA (MulEquiv.isField (Field.toIsField (Spec (.of A)).functionField)
    (e₂.symm.trans e₁).toMulEquiv)

/-- The property carried along a Zariski sequence. -/
private def Good (Y : Scheme.{u}) (g : Spec (.of A) ⟶ Y) : Prop :=
  IsIntegral Y ∧ IsLocallyNoetherian Y ∧ IsGenericPoint (g (genericPoint (Spec (.of A))))
    Set.univ ∧ Function.Bijective (g.stalkMap (genericPoint (Spec (.of A))))

private lemma good_of_comp {W Y : Scheme.{u}} (g : Spec (.of A) ⟶ W) (e : W ⟶ Y)
    [IsOpenImmersion e] (h : Good Y (g ≫ e)) : Good W g := by
  obtain ⟨hY, hYn, ha, hb⟩ := h
  have : Nonempty W := ⟨g (genericPoint _)⟩
  have hW : IsIntegral W := isIntegral_of_isOpenImmersion e
  refine ⟨hW, isLocallyNoetherian_of_isOpenImmersion e, ?_, ?_⟩
  · have h1 : e (g (genericPoint _)) = e (genericPoint W) := by
      rw [genericPoint_eq_of_isOpenImmersion e]
      exact ha.eq (genericPoint_spec Y)
    rw [e.isOpenEmbedding.injective h1]
    exact genericPoint_spec W
  · have hb' : Function.Bijective ((g.stalkMap _).hom ∘ (e.stalkMap (g (genericPoint _))).hom) := by
      rwa [Scheme.Hom.stalkMap_comp] at hb
    exact (Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso _)).mp hb'

private lemma centerIdeal_ne_bot [IsLocalRing A] (hA : ¬ IsField A) {Y : Scheme.{u}}
    (g : Spec (.of A) ⟶ Y) (hg : Good Y g) : centerIdeal g ≠ ⊥ := by
  intro hI
  have h := support_centerIdeal g
  rw [hI, Scheme.IdealSheafData.support_bot] at h
  exact not_isGenericPoint_closedPoint g hA hg.2.2.1 hg.2.2.2.2
    (isGenericPoint_def.mpr (h.symm.trans TopologicalSpace.Closeds.coe_top))

/-- A point of the blow-up over the generic point of the base is the generic point. -/
private lemma eq_genericPoint_of_blowUpToBase_eq {Y : Scheme.{u}} [IsIntegral Y]
    (I : Y.IdealSheafData) (hI : I ≠ ⊥) [IsIntegral (blowUp I)] (z : blowUp I)
    (hz : blowUpToBase I z = genericPoint Y) : z = genericPoint (blowUp I) := by
  let W : Y.Opens := ⟨(I.support : Set Y)ᶜ, I.support.isClosed.isOpen_compl⟩
  have hiso : IsIso (blowUpToBase I ∣_ W) := isIso_blowUp_restrict_compl_support I
  have hgW : genericPoint Y ∈ W := genericPoint_notMem_supportSet I hI
  have hzV : z ∈ blowUpToBase I ⁻¹ᵁ W := by
    change blowUpToBase I z ∈ W
    rw [hz]
    exact hgW
  have hgen : genericPoint (blowUp I) ∈ blowUpToBase I ⁻¹ᵁ W :=
    ((genericPoint_spec _).mem_open_set_iff (Opens.isOpen _)).mpr ⟨z, trivial, hzV⟩
  have hbgen : blowUpToBase I (genericPoint (blowUp I)) = genericPoint Y := by
    have := (isBirational_blowUpToBase I hI).bijOn.mapsTo
      (show genericPoint (blowUp I) ∈ genericPoints (blowUp I) by
        simp [genericPoints_eq_singleton])
    simpa [genericPoints_eq_singleton] using this
  have key : ∀ p : (blowUpToBase I ⁻¹ᵁ W).toScheme,
      W.ι ((blowUpToBase I ∣_ W) p) = blowUpToBase I p.1 := fun p => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι]
    rfl
  have : (⟨z, hzV⟩ : (blowUpToBase I ⁻¹ᵁ W).toScheme) = ⟨genericPoint _, hgen⟩ :=
    (blowUpToBase I ∣_ W).isOpenEmbedding.injective <| W.ι.isOpenEmbedding.injective <|
      (key _).trans (hz.trans (hbgen.symm.trans (key ⟨_, hgen⟩).symm))
  exact congrArg Subtype.val this

private lemma good_blowUp [IsLocalRing A] (hA : ¬ IsField A) {Y : Scheme.{u}}
    (g : Spec (.of A) ⟶ Y) (hg : Good Y g) (h : Spec (.of A) ⟶ blowUp (centerIdeal g))
    (hh : h ≫ blowUpToBase (centerIdeal g) = g) : Good (blowUp (centerIdeal g)) h := by
  have hI := centerIdeal_ne_bot hA g hg
  obtain ⟨hY, hYn, ha, hb⟩ := hg
  have hBI : IsIntegral (blowUp (centerIdeal g)) := isIntegral_blowUp _ hI
  have hz : h (genericPoint _) = genericPoint (blowUp (centerIdeal g)) :=
    eq_genericPoint_of_blowUpToBase_eq _ hI _ (by
      rw [← Scheme.Hom.comp_apply, hh]
      exact ha.eq (genericPoint_spec Y))
  refine ⟨hBI, LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase _), ?_, ?_⟩
  · rw [hz]
    exact genericPoint_spec _
  · have hb' : Function.Bijective ((h.stalkMap _).hom ∘
        ((blowUpToBase (centerIdeal g)).stalkMap (h (genericPoint _))).hom) := by
      rwa [← hh, Scheme.Hom.stalkMap_comp] at hb
    have : IsIso ((blowUpToBase (centerIdeal g)).stalkMap (h (genericPoint _))) := by
      rw [hz]
      exact (isBirational_blowUpToBase _ hI).isIso_stalkMap _
        (by simp [genericPoints_eq_singleton])
    exact (Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso _)).mp hb'

private lemma exists_lift [ValuationRing A] (hA : ¬ IsField A) {Y : Scheme.{u}}
    (g : Spec (.of A) ⟶ Y) (hg : Good Y g) :
    ∃ h : Spec (.of A) ⟶ blowUp (centerIdeal g), h ≫ blowUpToBase (centerIdeal g) = g := by
  have hI := centerIdeal_ne_bot hA g hg
  obtain ⟨hY, hYn, ha, hb⟩ := hg
  set I := centerIdeal g
  set b := blowUpToBase I
  let K := FractionRing A
  let ι : Spec (.of K) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A K))
  let W : Y.Opens := ⟨(I.support : Set Y)ᶜ, I.support.isClosed.isOpen_compl⟩
  have hiso : IsIso (b ∣_ W) := isIso_blowUp_restrict_compl_support I
  have hrange : Set.range (ι ≫ g) ⊆ Set.range W.ι := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply,
      Spec_map_apply_eq_genericPoint _ (IsFractionRing.injective A K),
      ha.eq (genericPoint_spec Y)]
    exact genericPoint_notMem_supportSet I hI
  let i₁ : Spec (.of K) ⟶ blowUp I :=
    IsOpenImmersion.lift W.ι (ι ≫ g) hrange ≫ inv (b ∣_ W) ≫ (b ⁻¹ᵁ W).ι
  have hi₁ : i₁ ≫ b = ι ≫ g := by
    simp only [i₁, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
      IsOpenImmersion.lift_fac]
  have hE : ValuativeCriterion.Existence b :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed b)).1
  obtain ⟨⟨⟨l, -, hl⟩⟩⟩ := hE { R := A, K := K, i₁ := i₁, i₂ := g, commSq := ⟨hi₁⟩ }
  exact ⟨l, hl⟩

private lemma good_fromSpecOfStalkLE {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (x₀ : X) (R : Subring X.functionField)
    (hS : ∀ s : X.presheaf.stalk x₀, algebraMap (X.presheaf.stalk x₀) X.functionField s ∈ R) :
    Good X (fromSpecOfStalkLE x₀ R hS) := by
  let ι : Spec (.of X.functionField) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom R.subtype)
  have hι : ι ≫ fromSpecOfStalkLE x₀ R hS = X.fromSpecStalk (genericPoint X) := by
    rw [fromSpecOfStalkLE, ← Category.assoc, ← Spec.map_comp,
      ← X.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes trivial)]
    rfl
  let pt : Spec (.of X.functionField) := closedPoint X.functionField
  have hpt : ι pt = genericPoint (Spec (.of R)) :=
    Spec_map_apply_eq_genericPoint _ Subtype.val_injective _
  refine ⟨‹_›, ‹_›, ?_, ?_⟩
  · rw [← hpt, ← Scheme.Hom.comp_apply, hι]
    have hgen : X.fromSpecStalk (genericPoint X) pt = genericPoint X :=
      Scheme.fromSpecStalk_closedPoint
    rw [hgen]
    exact genericPoint_spec X
  · have h1 : Function.Bijective ((ι ≫ fromSpecOfStalkLE x₀ R hS).stalkMap pt) := by
      rw [hι]
      haveI := isIso_stalkMap_fromSpecStalk (genericPoint X) pt
      exact ConcreteCategory.bijective_of_isIso _
    have h1' : Function.Bijective ((ι.stalkMap pt).hom ∘
        ((fromSpecOfStalkLE x₀ R hS).stalkMap (ι pt)).hom) := by
      rwa [Scheme.Hom.stalkMap_comp] at h1
    have hfield : IsField ((Spec (.of R)).presheaf.stalk (ι pt)) := by
      rw [hpt]
      exact Field.toIsField (Spec (.of R)).functionField
    letI := hfield.toField
    have h2 : Function.Bijective ((fromSpecOfStalkLE x₀ R hS).stalkMap (ι pt)) :=
      ⟨h1'.1.of_comp, fun t => by
        obtain ⟨s, hs⟩ := h1'.2 ((ι.stalkMap pt).hom t)
        exact ⟨s, (ι.stalkMap pt).hom.injective hs⟩⟩
    rwa [hpt] at h2

private lemma good_topIso_inv {Y : Scheme.{u}} {g : Spec (.of A) ⟶ Y} (hg : Good Y g) :
    Good (⊤ : Y.Opens) (g ≫ (Scheme.topIso Y).inv) :=
  good_of_comp _ (Scheme.topIso Y).hom (by simpa using hg)

end Zariski

/-! ### The valuation ring of a divisor -/

section ValuationRing

universe v

open MMP.Flips

/-- A valuation of `K` with values in `ℤᵐ⁰` taking the value `exp (-1)` is rank-one discrete. -/
private theorem isRankOneDiscrete_of_exists_eq_exp_neg_one {K : Type*} [Ring K]
    (v : Valuation K ℤᵐ⁰) (hv : ∃ g, v g = WithZero.exp (-1)) : v.IsRankOneDiscrete := by
  obtain ⟨g, hval⟩ := hv
  refine ⟨⟨Units.mk0 (WithZero.exp (-1)) WithZero.exp_ne_zero, le_antisymm ?_ ?_, ?_⟩⟩
  · rw [Subgroup.zpowers_le]
    exact MonoidWithZeroHom.mem_valueGroup _ ⟨g, by simpa using hval⟩
  · intro γ _
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨-(γ : ℤᵐ⁰).log, Units.ext ?_⟩
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul,
      mul_one, neg_neg, WithZero.exp_log γ.ne_zero]
  · change WithZero.exp (-1 : ℤ) < 1
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega

/-- A ring map from a local ring into a field, landing in the valuation ring of `w` and sending the
maximal ideal into the maximal ideal of `w`, is a local homomorphism into the valuation ring. -/
private theorem isLocalHom_codRestrict_valuationSubring {A K Γ₀ : Type*} [CommRing A]
    [IsLocalRing A] [Field K] [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation K Γ₀) (φ : A →+* K) (h1 : ∀ a, w (φ a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal A, w (φ a) < 1) :
    IsLocalHom (φ.codRestrict w.valuationSubring.toSubring
      fun a => (w.mem_valuationSubring_iff _).2 (h1 a)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hlt := h2 a ((IsLocalRing.mem_maximalIdeal _).2 hna)
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have hb' : φ a * (b : K) = 1 := congrArg Subtype.val hb
  have := mul_lt_one_of_lt_of_le hlt ((w.mem_valuationSubring_iff _).1 b.2)
  rw [← map_mul, hb', map_one] at this
  exact lt_irrefl _ this

/-- **The point dimension formula for a divisor.** The residue field of the valuation ring `R`
of a divisor `(Y, f, E)` over a variety `X` has transcendence degree `dim X - 1` over `k`: `R` is
the local ring `𝒪_{Y,E}`, whose residue field `κ(η_E)` has transcendence degree
`dim Y - dim 𝒪_{Y,E} = dim X - 1`. -/
private theorem trdeg_residueField_add_one_eq {k : Type v} [Field k] {X : Scheme.{v}}
    [X.Over (Spec (.of k))] [IsIntegral X] (hX : Mori.IsVariety k (X ↘ Spec (.of k)))
    (D : ProperDivisorOver k (X ↘ Spec (.of k))) (x₀ : X) (hx₀ : x₀ = D.f D.E.genericPoint)
    (R : Subring X.functionField) [IsDiscreteValuationRing R]
    (hRv : ∀ g, g ∈ R ↔ D.valuation g ≤ 1)
    (hR : ∀ s : X.presheaf.stalk x₀, algebraMap (X.presheaf.stalk x₀) X.functionField s ∈ R) :
    letI : Algebra k (IsLocalRing.ResidueField R) :=
      ((IsLocalRing.residue R).comp
        (((algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict R hR).comp
          ((X.presheaf.germ ⊤ x₀ trivial).hom.comp
            ((X ↘ Spec (.of k)).appTop.hom.comp
              (Scheme.ΓSpecIso (.of k)).inv.hom)))).toAlgebra
    (((Algebra.trdeg k (IsLocalRing.ResidueField R)).toENat + 1 : ℕ∞) : WithBot ℕ∞) =
      topologicalKrullDim X := by
  subst hx₀
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : LocallyOfFiniteType (X ↘ Spec (.of k)) := hX.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (D.f ≫ X ↘ Spec (.of k)) :=
    D.isNormalVariety.1.toLocallyOfFiniteType
  haveI := D.E.isDiscreteValuationRing_localRing
  have hbij := MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective D.isBirationalMorphism
  -- `dim D.Y = dim X`, and the point dimension formula at the generic point of `E`
  have hdimY : topologicalKrullDim D.Y = topologicalKrullDim X := by
    rw [← toENat_trdeg_functionField (sX := D.f ≫ X ↘ Spec (.of k)),
      ← toENat_trdeg_functionField (sX := X ↘ Spec (.of k)),
      trdeg_functionField_eq_of_bijective _ D.f hbij]
  have hη := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k D.Y
    (D.f ≫ X ↘ Spec (.of k)) D.E.genericPoint
  rw [← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k D.Y
    (D.f ≫ X ↘ Spec (.of k)) D.E.genericPoint, hdimY, ringKrullDim_stalk_eq_coheight,
    D.E.coheight_genericPoint] at hη
  rw [hη]
  -- the valuation ring `R` is the local ring `𝒪_{D.Y, E}`
  let ffm := RingEquiv.ofBijective _ hbij
  let O := D.Y.presheaf.stalk D.E.genericPoint
  have hmem : ∀ r : O, ffm.symm (algebraMap O D.Y.functionField r) ∈ R := fun r => by
    refine (hRv _).2 ?_
    change D.E.divisorialValuation (ffm (ffm.symm _)) ≤ 1
    rw [RingEquiv.apply_symm_apply]
    exact (MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff _ _).2 ⟨r, rfl⟩
  let φ : O →+* R := (ffm.symm.toRingHom.comp (algebraMap O D.Y.functionField)).codRestrict R hmem
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b hab => ?_, fun g => ?_⟩
    · have h := congrArg (fun x : R => ffm (x : X.functionField)) hab
      simp only [φ, RingHom.codRestrict_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at h
      exact IsFractionRing.injective O D.Y.functionField h
    · obtain ⟨r, hr⟩ := (MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff _ _).1
        ((hRv g).1 g.2)
      refine ⟨r, Subtype.ext ?_⟩
      change ffm.symm (algebraMap O D.Y.functionField r) = g
      rw [hr]
      exact ffm.symm_apply_apply g
  let Φ := RingEquiv.ofBijective φ hφ
  letI : Algebra k (D.Y.residueField D.E.genericPoint) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.f ≫ X ↘ Spec (.of k)).appTop ≫
      D.Y.Γevaluation D.E.genericPoint).hom.toAlgebra
  letI : Algebra k (IsLocalRing.ResidueField R) :=
    ((IsLocalRing.residue R).comp
      (((algebraMap (X.presheaf.stalk (D.f D.E.genericPoint)) X.functionField).codRestrict R
        hR).comp ((X.presheaf.germ ⊤ (D.f D.E.genericPoint) trivial).hom.comp
          ((X ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)))).toAlgebra
  let eκ : D.Y.residueField D.E.genericPoint ≃ₐ[k] IsLocalRing.ResidueField R :=
    { IsLocalRing.ResidueField.mapEquiv Φ with
      commutes' := fun c => by
        set a := (X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c)
        change IsLocalRing.ResidueField.map (Φ : O →+* R)
          (IsLocalRing.residue O (D.Y.presheaf.germ ⊤ D.E.genericPoint trivial (D.f.appTop a))) =
          IsLocalRing.residue R _
        rw [IsLocalRing.ResidueField.map_residue]
        congr 1
        refine Subtype.ext ?_
        change ffm.symm _ = algebraMap (X.presheaf.stalk (D.f D.E.genericPoint)) X.functionField
          (X.presheaf.germ ⊤ (D.f D.E.genericPoint) trivial a)
        rw [RingEquiv.symm_apply_eq]
        change _ = functionFieldMap D.f _
        rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
        congr 1
        exact (Scheme.Hom.germ_stalkMap_apply D.f ⊤ D.E.genericPoint trivial a).symm }
  rw [← eκ.trdeg_eq]
  norm_cast

end ValuationRing

/-! ### Birational morphisms -/

section Birational

/-- Precomposing a normal variety with an isomorphism gives a normal variety. -/
private theorem isNormalVariety_comp_iso {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {s : Y ⟶ Spec (.of k)} (h : IsNormalVariety k s) (e : Y' ⟶ Y) [IsIso e] :
    IsNormalVariety k (e ≫ s) := by
  haveI : AlgebraicGeometry.IsVariety k s := h.1
  haveI : IsNormal Y := h.2
  haveI : IsIntegral Y := h.1.toIsIntegral
  haveI : Nonempty Y' := ⟨(inv e) (Nonempty.some (inferInstance : Nonempty Y))⟩
  haveI : IsIntegral Y' := isIntegral_of_isOpenImmersion e
  refine ⟨{}, ⟨fun y => ?_, fun y => ?_⟩⟩
  · haveI : IsIso (e.stalkMap y) := IsOpenImmersion.instIsIsoCommRingCatStalkMap e y
    haveI := IsNormal.stalk_isDomain (X := Y) (e y)
    exact MulEquiv.isDomain _ (asIso (e.stalkMap y)).commRingCatIsoToRingEquiv.symm.toMulEquiv
  · haveI : IsIso (e.stalkMap y) := IsOpenImmersion.instIsIsoCommRingCatStalkMap e y
    haveI := IsNormal.stalk_normal (X := Y) (e y)
    exact IsIntegrallyClosed.of_equiv (asIso (e.stalkMap y)).commRingCatIsoToRingEquiv

end Birational

/-! ### Exceptional divisors and coheights -/

section Exceptional

open MMP.Flips

private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + c = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_add, top_add]
      rw [this] at h
      exact ENat.top_ne_natCast n (WithBot.coe_injective h)
    | coe d =>
      induction c using ENat.recTopCoe with
      | top =>
        exfalso
        have : ((d : ℕ∞) : WithBot ℕ∞) + ((⊤ : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
          rw [← WithBot.coe_add, add_top]
        rw [this] at h
        exact ENat.top_ne_natCast n (WithBot.coe_injective h)
      | coe c =>
        have h' : d + c = n := by exact_mod_cast h
        have e1 : (((d : ℕ∞) : WithBot ℕ∞) + 2 ≤ (n : WithBot ℕ∞)) ↔ d + 2 ≤ n := by
          rw [show ((d : ℕ∞) : WithBot ℕ∞) + 2 = (((d + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) from rfl,
            show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, WithBot.coe_le_coe,
            Nat.cast_le]
        rw [e1]
        constructor
        · intro h2; exact_mod_cast (show 2 ≤ c by omega)
        · intro h2; have : 2 ≤ c := by exact_mod_cast h2
          omega

private theorem properDivisorOver_isExceptional_iff {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : ProperDivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  unfold ProperDivisorOver.IsExceptional
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff h

/-- A prime divisor `E` of a normal scheme `W` is exceptional for a morphism `g : W ⟶ T` to a
separated normal scheme exactly when `g(η_E)` has coheight at least two. -/
private theorem isExceptional_toRationalMap_iff_two_le_coheight {W T : Scheme.{u}}
    [IsLocallyNoetherian W] [IsNormal W] [IsLocallyNoetherian T] [IsNormal T]
    [IsSeparated (T ↘ ⊤_ Scheme)] (g : W ⟶ T) (E : MMP.Mori.PrimeDivisor W) :
    RationalMap.IsExceptional (X := W) g.toRationalMap E ↔
      2 ≤ Order.coheight (g E.genericPoint) := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (g '' (E.idealSheaf.support : Set W)) =
      ⟨((IrreducibleCloseds.closureSingleton (g E.genericPoint) : IrreducibleCloseds T) : Set T),
        (IrreducibleCloseds.closureSingleton (g E.genericPoint)).isClosed⟩ := by
    ext1
    change closure (g '' E.support) = closure {g E.genericPoint}
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine le_antisymm ?_ (closure_mono ?_)
    · refine closure_minimal ?_ isClosed_closure
      refine (image_closure_subset_closure_image g.continuous).trans ?_
      rw [Set.image_singleton]
    · rw [Set.singleton_subset_iff]
      exact ⟨E.genericPoint, subset_closure rfl, rfl⟩
  rw [hcl, closedsCodimension_coe, codimension_eq_coheight,
    show IrreducibleCloseds.closureSingleton (g E.genericPoint) =
      (irreducibleSetEquivPoints (α := T)).symm (g E.genericPoint) from rfl,
    Order.coheight_orderIso]

end Exceptional

/-! ### Prime divisors in snc closed subsets -/

section SNCHelpers

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- The reduced divisor with components a finite set `s` of prime divisors has support `s`. -/
private theorem support_sum_single {X : Scheme.{u}} (s : Finset (Mori.PrimeDivisor X)) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor X).support = s := by
  classical
  ext E
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- A prime divisor whose generic point lies in a closed set is contained in it. -/
private theorem support_subset_of_genericPoint_mem {X : Scheme.{u}} (P : Mori.PrimeDivisor X)
    {C : Set X} (hC : IsClosed C) (h : P.genericPoint ∈ C) : (P.support : Set X) ⊆ C := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact closure_minimal (Set.singleton_subset_iff.mpr h) hC

/-- The ideal sheaf of a prime divisor is the vanishing ideal of its support. -/
private theorem idealSheaf_eq_vanishingIdeal {X : Scheme.{u}} (P : Mori.PrimeDivisor X)
    {T : Closeds X} (hT : (T : Set X) = P.support) :
    P.idealSheaf = Scheme.IdealSheafData.vanishingIdeal T := by
  have := P.integral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ (Closeds.ext hT.symm)

/-- An irreducible component of a closed subset of pure codimension one is the closure of a
point of coheight one. -/
private theorem exists_coheight_eq_one_of_mem_componentsOf {S : Set Y} (hSc : IsClosed S)
    (hS : MMP.Mori.IsPureCodimOne (⟨S, hSc⟩ : Closeds Y)) {V : Set Y}
    (hV : V ∈ componentsOf S) : ∃ ξ : Y, V = closure {ξ} ∧ Order.coheight ξ = 1 := by
  obtain ⟨ξ, -, hξ⟩ := Aux.exists_eq_closure_of_mem_componentsOf hSc hV
  refine ⟨ξ, hξ, ?_⟩
  rw [← MMP.Flips.codimension_closureSingleton]
  apply hS
  refine ⟨?_, fun W' hW' hle => ?_⟩
  · change closure {ξ} ⊆ S
    rw [← hξ]
    exact hV.1.2
  · have : (W' : Set Y) ⊆ V := hV.2 ⟨W'.isIrreducible, hW'⟩ (by rwa [hξ])
    change (W' : Set Y) ⊆ closure {ξ}
    rw [← hξ]
    exact this

/-- The support of a prime divisor contained in an snc closed subset `S` is an irreducible
component of `S`. -/
private theorem support_mem_componentsOf [NoetherianSpace Y] {S : Set Y}
    (hS : IsSNCClosedSubset sY S) {P : Mori.PrimeDivisor Y} (hP : (P.support : Set Y) ⊆ S) :
    (P.support : Set Y) ∈ componentsOf S := by
  obtain ⟨hSc, hempty | ⟨hpure, -, -⟩⟩ := hS
  · exfalso
    have := hP (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P)
    rw [hempty] at this
    exact this
  · obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf hSc
    obtain ⟨W, hW, hηW⟩ := hcov (hP (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P))
    obtain ⟨ξ, hWξ, hξ1⟩ := exists_coheight_eq_one_of_mem_componentsOf hSc hpure hW
    have hsp : ξ ⤳ P.genericPoint := specializes_iff_mem_closure.mpr (hWξ ▸ hηW)
    have hξη : ξ = P.genericPoint := by
      by_contra hne
      have hlt : P.genericPoint < ξ := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp)
        fun hle => hne (hsp.antisymm (Scheme.le_iff_specializes.mp hle)).eq
      have := Order.coheight_strictAnti hlt
      rw [hξ1, P.coheight_genericPoint] at this
      exact lt_irrefl _ (this (by simp))
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    change closure {P.genericPoint} ∈ _
    rw [← hξη, ← hWξ]
    exact hW

/-- Only finitely many prime divisors are contained in an snc closed subset. -/
private theorem finite_setOf_support_subset [NoetherianSpace Y] {S : Set Y}
    (hS : IsSNCClosedSubset sY S) :
    {P : Mori.PrimeDivisor Y | (P.support : Set Y) ⊆ S}.Finite := by
  refine Set.Finite.of_finite_image ((Aux.finite_and_cover_componentsOf hS.1).1.subset ?_)
    fun P _ Q _ h => MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset h.subset
  rintro - ⟨P, hP, rfl⟩
  exact support_mem_componentsOf hS hP

/-- **A reduced divisor whose components lie in an snc closed subset is snc.** -/
private theorem isSNC_sum_single_of_support_subset [LocallyOfFiniteType sY] [NoetherianSpace Y]
    [IsLocallyNoetherian Y] (hsm : IsSmoothScheme sY) {S : Set Y} (hS : IsSNCClosedSubset sY S)
    (s : Finset (Mori.PrimeDivisor Y)) (hs : ∀ P ∈ s, (P.support : Set Y) ⊆ S) :
    (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).IsSNC sY := by
  classical
  have hc : ∀ P ∈ s, (P.support : Set Y) ∈ componentsOf S := fun P hP =>
    support_mem_componentsOf hS (hs P hP)
  obtain ⟨hSc, hempty | ⟨-, -, hfam⟩⟩ := id hS
  · have hs0 : s = ∅ := Finset.eq_empty_of_forall_notMem fun P hP => by
      have := hs P hP (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P)
      rw [hempty] at this
      exact this
    subst hs0
    rw [Finset.sum_empty]
    exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme sY hsm
  have hG := support_sum_single s
  have hideal : ∀ P (hP : P ∈ s),
      P.idealSheaf = componentsFamily S ⟨(P.support : Set Y), hc P hP⟩ := fun P hP =>
    idealSheaf_eq_vanishingIdeal P (by
      rw [Closeds.coe_closure, (Aux.isClosed_of_mem_componentsOf hSc (hc P hP)).closure_eq])
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [hG] at hP
    rw [hideal P hP]
    exact (hfam.1 _).2.2
  · obtain ⟨m, z, c, hz, hcI, hcinj⟩ := hfam.2 x
    have hs' : ∀ P : {P : Mori.PrimeDivisor Y //
        P ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ x ∈ P.support},
        P.1 ∈ s := fun P => hG.subset P.2.1
    have hmem : ∀ P : {P : Mori.PrimeDivisor Y //
        P ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ x ∈ P.support},
        x ∈ (componentsFamily S ⟨(P.1.support : Set Y), hc P.1 (hs' P)⟩).support := fun P => by
      rw [← SetLike.mem_coe, coe_support_componentsFamily hSc]
      exact P.2.2
    refine ⟨m, z, fun P => c ⟨_, hmem P⟩, hz, fun P Q h => ?_, fun P => ?_⟩
    · have h1 := congrArg (fun V => (V.1.1 : Set Y)) (hcinj h)
      exact Subtype.ext (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset h1.subset)
    · rw [hideal P.1 (hs' P)]
      exact hcI ⟨_, hmem P⟩

end SNCHelpers

/-! ### The coefficient-one boundary and the invariants of a model -/

section Setup

variable {X : Scheme.{u}}

/-- The support `⋃_{coeff_D B = 1} D` of the coefficient-one part of an `ℝ`-divisor `B`. -/
private def oneLocus (B : RDivisor X) : Set X :=
  {x | ∃ D : Mori.PrimeDivisor X, B.coeff D = 1 ∧ x ∈ D.support}

open Classical in
/-- The reduced coefficient-one part `⌊B⌋ = ∑_{coeff_D B = 1} D` of an `ℝ`-divisor `B`, as a
`ℚ`-divisor. -/
private noncomputable def oneDivisor (B : RDivisor X) : QDivisor X :=
  ∑ P ∈ B.support.filter (fun P => B.coeff P = 1), Finsupp.single P 1

/-- `(q, y)` lies in the smallest class of pairs containing `(𝟙 X, x)`, closed under
precomposition with isomorphisms and under blowing up the reduced closure of a stratum of
`q⁻¹(⌊B⌋)` through the image of the point. -/
private def IsStratumReached (B : RDivisor X) {Y : Scheme.{u}} (q : Y ⟶ X) (y : Y) : Prop :=
  ∀ P : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Y → Prop, (∀ x : X, P (𝟙 X) x) →
    (∀ {Y Y' : Scheme.{u}} (e : Y' ⟶ Y) [IsIso e] (q : Y ⟶ X) (y : Y'), P q (e y) →
      P (e ≫ q) y) →
    (∀ {Y : Scheme.{u}} (q : Y ⟶ X) (Z : Y.IdealSheafData) (y : blowUp Z),
      P q (blowUpToBase Z y) →
      (∃ J : Set (Set Y), J.Nonempty ∧ J ⊆ componentsOf (q ⁻¹' oneLocus B) ∧
        (Z.support : Set Y) ∈ componentsOf (⋂₀ J)) →
      Z = Scheme.IdealSheafData.vanishingIdeal Z.support → blowUpToBase Z y ∈ Z.support →
      P (blowUpToBase Z ≫ q) y) → P q y

/-- A prime divisor lies over the coefficient-one locus exactly when it is a coefficient-one
component. -/
private theorem genericPoint_mem_oneLocus_iff {B : RDivisor X} (G : Mori.PrimeDivisor X) :
    G.genericPoint ∈ oneLocus B ↔ B.coeff G = 1 := by
  constructor
  · rintro ⟨D, hD, hGD⟩
    rwa [MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset
      (support_subset_of_genericPoint_mem G (SNCWeight.PrimeDivisorUnion.isClosed_support D) hGD)]
  · intro h
    exact ⟨G, h, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' G⟩

/-- The coefficient-one locus lies in the support. -/
private theorem oneLocus_subset_supp (B : RDivisor X) : oneLocus B ⊆ (B.supp : Set X) := by
  rintro x ⟨D, hD, hxD⟩
  exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨D, by rw [hD]; exact one_ne_zero, hxD⟩

/-- A prime divisor of `Y` whose generic point maps to the coefficient-one locus maps into it. -/
private theorem support_subset_preimage_oneLocus {B : RDivisor X} {Y : Scheme.{u}} (q : Y ⟶ X)
    (G : Mori.PrimeDivisor Y) (h : q G.genericPoint ∈ oneLocus B) :
    (G.support : Set Y) ⊆ q ⁻¹' oneLocus B := by
  obtain ⟨D, hD1, hGD⟩ := h
  exact fun x hx => ⟨D, hD1, support_subset_of_genericPoint_mem G
    ((SNCWeight.PrimeDivisorUnion.isClosed_support D).preimage q.continuous) hGD hx⟩

/-- A prime divisor of `Y` whose generic point maps to the coefficient-one locus maps into the
support. -/
private theorem support_subset_preimage_supp {B : RDivisor X} {Y : Scheme.{u}} (q : Y ⟶ X)
    (G : Mori.PrimeDivisor Y) (h : q G.genericPoint ∈ oneLocus B) :
    (G.support : Set Y) ⊆ q ⁻¹' B.supp :=
  (support_subset_preimage_oneLocus q G h).trans (Set.preimage_mono (oneLocus_subset_supp B))

/-- The coefficients of the reduced coefficient-one part. -/
private theorem coeff_oneDivisor (B : RDivisor X) (G : Mori.PrimeDivisor X) :
    (oneDivisor B).coeff G = if B.coeff G = 1 then 1 else 0 := by
  classical
  unfold oneDivisor
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finsupp.mem_support_iff]
  by_cases h : B.coeff G = 1
  · rw [if_pos ⟨by rw [← DivisorWithCoeffs.coeff_apply, h]; exact one_ne_zero, h⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.2), if_neg h]

end Setup

/-! ### Strata of snc divisors and their blow-ups -/

section Stratum

open MMP.Fourfold.SNCWeight

private theorem stalk_bot_eq {Y : Scheme.{u}} (x : Y) :
    IdealSheafData.stalk (⊥ : Y.IdealSheafData) x = ⊥ := by
  rw [IdealSheafData.stalk]
  refine le_bot_iff.mp (iSup₂_le fun U hs => ?_)
  rw [show (⊥ : Y.IdealSheafData).ideal U = ⊥ from rfl, Ideal.map_bot]

/-- The stalk of a finite supremum of ideal sheaves is the supremum of the stalks. -/
private theorem stalk_finset_sup {Y : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (f : ι → Y.IdealSheafData) (x : Y) :
    IdealSheafData.stalk (s.sup f) x = ⨆ i ∈ s, IdealSheafData.stalk (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, stalk_bot_eq]
    symm
    simp only [iSup_eq_bot]
    intro i hi
    exact absurd hi (Finset.notMem_empty i)
  | insert i s hi ih =>
    rw [Finset.sup_insert, IdealSheafData.stalk_sup, ih, Finset.iSup_insert]

/-- The support of a finite supremum of ideal sheaves is the intersection of the supports. -/
private theorem coe_support_finset_sup {Y : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (f : ι → Y.IdealSheafData) :
    ((s.sup f).support : Set Y) = ⋂ i ∈ s, ((f i).support : Set Y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sup_insert, Scheme.IdealSheafData.support_sup, Closeds.coe_inf, ih,
      Finset.set_biInter_insert]

/-- A supremum of principal ideals generated by members `z_j`, `j ∈ J`, of a family. -/
private theorem iSup_eq_span_image {R : Type*} [CommRing R] {N : ℕ} (z : Fin N → R)
    {ι : Type*} (T : Finset ι) (I : ι → Ideal R) (J : Finset (Fin N))
    (h1 : ∀ G ∈ T, ∃ j ∈ J, I G = Ideal.span {z j})
    (h2 : ∀ j ∈ J, ∃ G ∈ T, I G = Ideal.span {z j}) :
    ⨆ G ∈ T, I G = Ideal.span (z '' (J : Set (Fin N))) := by
  refine le_antisymm (iSup₂_le fun G hG => ?_) (Ideal.span_le.mpr ?_)
  · obtain ⟨j, hj, hIj⟩ := h1 G hG
    rw [hIj]
    exact Ideal.span_mono (Set.singleton_subset_iff.mpr ⟨j, hj, rfl⟩)
  · rintro _ ⟨j, hj, rfl⟩
    obtain ⟨G, hG, hIj⟩ := h2 j hj
    have : z j ∈ I G := by rw [hIj]; exact Ideal.mem_span_singleton_self _
    exact (le_iSup₂ (f := fun G _ => I G) G hG) this

end Stratum

end MMP.Fourfold.ZeroPlaceExtraction

namespace MMP.Fourfold

open MMP.Mori MMP.Resolution MMP.Fourfold.ZeroPlaceExtraction
open TopologicalSpace

section Stratum

open SNCWeight

variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- **The closure of a point of a stratum.** Let `∑_{G ∈ T} G` be an snc divisor on a scheme `Y`
smooth over a perfect field, and `y` a point of codimension `|T|` lying on every `G ∈ T`. Then
`closure {y}` is an irreducible component of `⋂_{G ∈ T} G`, it is smooth with its reduced
structure, and along it its ideal is `∑_{G ∈ T} I_G`. -/
theorem closure_singleton_mem_componentsOf_of_isSNC [PerfectField k] (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sY] [QuasiCompact sY] {T : Finset (Mori.PrimeDivisor Y)}
    (hsnc : DivisorWithCoeffs.IsSNC sY (∑ G ∈ T, Finsupp.single G (1 : ℤ)))
    {y : Y} (hyT : ∀ G ∈ T, y ∈ G.support) (hc : Order.coheight y = T.card) :
    closure {y} ∈ componentsOf (⋂ G ∈ T, (G.support : Set Y)) ∧
      IsSmoothScheme
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {y})).subschemeι ≫ sY) ∧
      ∀ x ∈ closure {y},
        IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {y})) x =
          ⨆ G ∈ T, IdealSheafData.stalk G.idealSheaf x := by
  classical
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := {}
  set D := T.sup (fun G => G.idealSheaf) with hDdef
  have hDsupp : (D.support : Set Y) = ⋂ G ∈ T, (G.support : Set Y) := coe_support_finset_sup _ _
  -- coordinates at a point of `D`
  have hcoord : ∀ x ∈ (D.support : Set Y), ∃ (N : ℕ) (z : Fin N → Y.presheaf.stalk x)
      (J : Finset (Fin N)), IsRegularSystemOfParameters z ∧ J.card = T.card ∧
        IdealSheafData.stalk D x = Ideal.span (z '' (J : Set (Fin N))) := by
    intro x hx
    rw [hDsupp, Set.mem_iInter₂] at hx
    obtain ⟨N, z, j, hz, hj, hI⟩ := exists_at_of_isSNC hsnc x
    let jT : T → Fin N := fun G => j ⟨G.1, G.2, hx G.1 G.2⟩
    have hjT : Function.Injective jT := fun G G' h =>
      Subtype.ext (congrArg Subtype.val (hj h) :)
    refine ⟨N, z, Finset.univ.image jT, hz, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hjT, Finset.card_univ, Fintype.card_coe]
    · rw [hDdef, stalk_finset_sup]
      refine iSup_eq_span_image z T _ _ (fun G hG => ⟨jT ⟨G, hG⟩,
        Finset.mem_image_of_mem _ (Finset.mem_univ _), hI ⟨G, hG, hx G hG⟩⟩) fun i hi => ?_
      obtain ⟨G, -, rfl⟩ := Finset.mem_image.mp hi
      exact ⟨G.1, G.2, hI ⟨G.1, G.2, hx G.1 G.2⟩⟩
  have hDreg : ∀ x ∈ D.support,
      IsRegularLocalRing (Y.presheaf.stalk x ⧸ IdealSheafData.stalk D x) := by
    intro x hx
    obtain ⟨N, z, J, hz, -, hDx⟩ := hcoord x hx
    have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
    rw [hDx]
    exact MMP.Resolution.isRegularLocalRing_quotient_span_image z hz J
  have hDsm : IsSmoothScheme (D.subschemeι ≫ sY) :=
    PrimeDivisorUnion.isSmoothScheme_subscheme_of_isRegularLocalRing_quotient sY D hDreg
  have hDred : IsReduced D.subscheme := by
    have : LocallyOfFinitePresentation (D.subschemeι ≫ sY) :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := D.subschemeι ≫ sY)).mpr
        inferInstance
    have hsm : Smooth (D.subschemeι ≫ sY) := (MMP.Mori.isSmoothScheme_iff _).1 hDsm
    haveI : ∀ x : D.subscheme, _root_.IsReduced (D.subscheme.presheaf.stalk x) := fun x => by
      have := isRegularLocalRing_stalk_of_smooth_over_field (D.subschemeι ≫ sY) x
      have := IsRegularLocalRing.isDomain (D.subscheme.presheaf.stalk x)
      exact isReduced_of_noZeroDivisors
    exact isReduced_of_isReduced_stalk _
  have hyD : y ∈ (D.support : Set Y) := by rw [hDsupp]; exact Set.mem_iInter₂.mpr hyT
  have hDcl : IsClosed (D.support : Set Y) := D.support.isClosed
  obtain ⟨hfin, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf hDcl
  obtain ⟨C, hC, hyC⟩ := hcov hyD
  -- the component through `y` is the closure of `y`
  obtain ⟨ξ, hξD, hCξ⟩ := MMP.Resolution.Aux.exists_eq_closure_of_mem_componentsOf hDcl hC
  have hξy : ξ = y := by
    have hsp : ξ ⤳ y := specializes_iff_mem_closure.mpr (hCξ ▸ hyC)
    obtain ⟨N, z, J, hz, hJ, -⟩ := hcoord ξ hξD
    have hJN : J.card ≤ N := by simpa using Finset.card_le_univ J
    have hle : (T.card : ℕ∞) ≤ Order.coheight ξ := by
      rw [coheight_eq_of_isRegularSystemOfParameters hz, ← hJ]
      exact_mod_cast hJN
    by_contra hne
    have hlt : y < ξ := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp)
      fun hle' => hne (hsp.antisymm (Scheme.le_iff_specializes.mp hle')).eq
    have hfin : Order.coheight ξ < ⊤ := by
      rw [coheight_eq_of_isRegularSystemOfParameters hz]; exact ENat.coe_lt_top _
    have := Order.coheight_strictAnti hlt hfin
    rw [hc] at this
    exact absurd (lt_of_lt_of_le this hle) (lt_irrefl _)
  rw [hξy] at hCξ
  subst hCξ
  have hCcl : IsClosed (closure {y} : Set Y) := isClosed_closure
  set B := ⋃₀ (componentsOf (D.support : Set Y) \ {closure {y}}) with hB
  have hBcl : IsClosed B := (hfin.subset Set.sdiff_subset).isClosed_sUnion
    fun W hW => MMP.Resolution.Aux.isClosed_of_mem_componentsOf hDcl hW.1
  have hdisj : ∀ x ∈ closure {y}, x ∉ B := by
    rintro x hxC ⟨W, ⟨hW, hWC⟩, hxW⟩
    exact hWC (MMP.Resolution.Aux.eq_of_mem_componentsOf_of_isSmoothScheme sY D hDsm hW hC
      hxW hxC)
  have hCB : closure {y} ∪ B = D.support := by
    refine le_antisymm (Set.union_subset hC.1.2 ?_) fun x hx => ?_
    · rintro x ⟨W, ⟨hW, -⟩, hxW⟩; exact hW.1.2 hxW
    · obtain ⟨W, hW, hxW⟩ := hcov hx
      by_cases h : W = closure {y}
      · exact Or.inl (h ▸ hxW)
      · exact Or.inr ⟨W, ⟨hW, h⟩, hxW⟩
  have hstalk : ∀ x ∈ closure {y}, IdealSheafData.stalk
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {y})) x =
        IdealSheafData.stalk D x := fun x hx =>
    MMP.Mori.stalk_vanishingIdeal_eq_stalk_of_sup_eq D (Closeds.closure {y}) ⟨B, hBcl⟩
      (Closeds.ext hCB) (hdisj x hx)
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {y})).support : Set Y) =
      closure {y} := by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]
  refine ⟨by rwa [← hDsupp], ?_, fun x hx => by rw [hstalk x hx, hDdef, stalk_finset_sup]⟩
  refine PrimeDivisorUnion.isSmoothScheme_subscheme_of_isRegularLocalRing_quotient sY _
    fun x hx => ?_
  rw [← SetLike.mem_coe, hsupp] at hx
  rw [hstalk x hx]
  exact hDreg x (hC.1.2 hx)

/-- **The centre has snc with the boundary.** If the ideal of `Z` is `∑_{G ∈ T} I_G` along `Z`,
for components `G ∈ T` of an snc divisor `D`, then `Z` has simple normal crossings with `D`. -/
private theorem hasSNCWith_of_stalk_eq {sY : Y ⟶ Spec (.of k)} [NoetherianSpace Y] {D : Set Y}
    (hD : IsSNCClosedSubset sY D) {Z : Y.IdealSheafData} {T : Finset (Mori.PrimeDivisor Y)}
    (hTne : T.Nonempty) (hTD : ∀ G ∈ T, (G.support : Set Y) ⊆ D)
    (hZT : ∀ G ∈ T, (Z.support : Set Y) ⊆ G.support)
    (hZst : ∀ x ∈ Z.support, IdealSheafData.stalk Z x =
      ⨆ G ∈ T, IdealSheafData.stalk G.idealSheaf x) :
    HasSNCWith (componentsFamily D) Z := by
  classical
  intro x hx
  have hGc : ∀ G ∈ T, (G.support : Set Y) ∈ componentsOf D := fun G hG =>
    support_mem_componentsOf hD (hTD G hG)
  obtain ⟨hDc, hempty | ⟨-, -, hfam⟩⟩ := hD
  · exfalso
    obtain ⟨G, hG⟩ := hTne
    have := hTD G hG (hZT G hG hx)
    rw [hempty] at this
    exact this
  have hideal : ∀ G (hG : G ∈ T), componentsFamily D ⟨_, hGc G hG⟩ = G.idealSheaf := fun G hG =>
    (idealSheaf_eq_vanishingIdeal G (by
      rw [Closeds.coe_closure, (Aux.isClosed_of_mem_componentsOf hDc (hGc G hG)).closure_eq])).symm
  have hmem : ∀ G (hG : G ∈ T), x ∈ (componentsFamily D ⟨_, hGc G hG⟩).support := fun G hG => by
    rw [hideal G hG]; exact hZT G hG hx
  obtain ⟨N, z, c, hz, hI, hcinj⟩ := hfam.2 x
  refine ⟨N, z, c, Finset.univ.filter
    (fun i => ∃ G, ∃ hG : G ∈ T, i = c ⟨⟨_, hGc G hG⟩, hmem G hG⟩), hz, hI, hcinj, ?_⟩
  rw [hZst x hx]
  refine iSup_eq_span_image z T _ _ (fun G hG => ⟨_, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, G, hG, rfl⟩, ?_⟩) fun i hi => ?_
  · rw [← hideal G hG]; exact hI ⟨⟨_, hGc G hG⟩, hmem G hG⟩
  · obtain ⟨-, G, hG, rfl⟩ := Finset.mem_filter.mp hi
    exact ⟨G, hG, by rw [← hideal G hG]; exact hI ⟨⟨_, hGc G hG⟩, hmem G hG⟩⟩

open scoped Classical in
open MMP.Threefold.Resolution MMP.Fourfold.SNCWeight.StratumBlowup
  MMP.Fourfold.SNCWeight.LocalEquation MMP.Fourfold.SNCWeight.BlowupCrepancy in
/-- **The exceptional divisor of a stratum blow-up is a zero place.** Let `Z` be a smooth centre
of codimension `c = |T|` on a smooth variety `Y` whose ideal is `∑_{G ∈ T} I_G` along `Z`, for the
components `G ∈ T` of an snc divisor, and let `Δ` have coefficient one along the `G ∈ T` and zero
along the other prime divisors through `Z`. Then the exceptional divisor `E` of `Bl_Z Y` has
discrepancy `a(E, Y, Δ) = (c - 1) - c = -1`. -/
theorem isDiscrepancy_excE_neg_one [PerfectField k] (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ} {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor sY n) {ΔY : QDivisor Y} (hPY : Mori.IsPair sY ΔY)
    {I : Y.IdealSheafData} (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
    {T : Finset (Mori.PrimeDivisor Y)}
    (hc : (T.card : ℕ∞) =
      codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (hc1 : 1 ≤ T.card)
    (hsnc : DivisorWithCoeffs.IsSNC sY (∑ G ∈ T, Finsupp.single G (1 : ℤ)))
    (hIT : ∀ G ∈ T, (I.support : Set Y) ⊆ G.support)
    (hIst : ∀ x ∈ I.support, IdealSheafData.stalk I x =
      ⨆ G ∈ T, IdealSheafData.stalk G.idealSheaf x)
    (hΔ : ∀ Γ : Mori.PrimeDivisor Y, (I.support : Set Y) ⊆ Γ.support →
      ΔY.coeff Γ = if Γ ∈ T then 1 else 0)
    (hN : IsNormalVariety k (blowUpToBase I ≫ sY))
    (hc1' : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (hb : haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc1'
      IsBirationalMorphism (blowUpToBase I)) :
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc1'
    IsDiscrepancy sY n KY ΔY ⟨blowUp I, blowUpToBase I, hN, hb, excE sY h hirr hc1'⟩ (-1) := by
  classical
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc1'
  haveI := isDominant_blowUpToBase I hirr hc1'
  haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
  haveI : Smooth sY := smooth_of_isSmoothScheme h.1
  set E := excE sY h hirr hc1' with hE
  set x₀ := blowUpToBase I E.genericPoint with hx₀
  have hx₀I : closure {x₀} = (I.support : Set Y) := closure_map_genericPoint_excE sY h hirr hc1'
  have hx₀mem : x₀ ∈ (I.support : Set Y) := hx₀I ▸ subset_closure rfl
  have hmemΓ : ∀ Γ : Mori.PrimeDivisor Y, x₀ ∈ Γ.support → (I.support : Set Y) ⊆ Γ.support :=
    fun Γ hx => hx₀I ▸ closure_minimal (Set.singleton_subset_iff.mpr hx)
      (PrimeDivisorUnion.isClosed_support Γ)
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPY hKY
    (⟨blowUp I, blowUpToBase I, hN, hb, E⟩ : DivisorOver k sY)
  suffices hae : a = -1 by rwa [hae] at ha
  have hn := hKY.topologicalKrullDim_eq
  obtain ⟨-, -, m, hm, -, U, hU, τ, hτ, hτa⟩ := ha
  -- generators of the top forms and the comparison along `E`
  obtain ⟨σA, hσA, h0A, σB, hσB, h0B, h', hrel, hh, hord⟩ :=
    MMP.Threefold.Resolution.exists_topForms_rel I sY h hirr hc hc1 hn E
  rw [if_pos rfl] at hord
  let := stalkAlgebra sY x₀
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY x₀
  have hordτ := MMP.Threefold.Resolution.ordForm_pullbackRationalPluriForms_eq sY
    (blowUpToBase I) E hσA h0A hσB h0B h' hrel hh hτ.1
  set g := formCoeff (k := k) (Y.presheaf.stalk x₀) hσA h0A
    (show PluriForms k Y.functionField n m from τ) with hgdef
  have hg0 : g ≠ 0 := fun h0 => hτ.1 ((formCoeff_eq_zero_iff hσA h0A _).mp h0)
  have hgΓ : ∀ Γ : Mori.PrimeDivisor Y, x₀ ∈ Γ.support →
      (Y.ord g Γ.genericPoint : ℝ) = -((m : ℝ) * (ΔY.coeff Γ : ℝ)) := by
    intro Γ hΓ
    have e1 := MMP.Threefold.Resolution.ordForm_eq_ord_formCoeff sY x₀ Γ hΓ hσA h0A τ
    have e2 := hτ.2 Γ ⟨_, hΓ, hU⟩
    rw [e1] at e2
    have := congrArg (fun q : ℚ => (q : ℝ)) e2
    push_cast at this
    linarith
  -- coordinates at the centre
  obtain ⟨N, z, j, hz, hj, hI⟩ := exists_at_of_isSNC hsnc x₀
  have hxT : ∀ G ∈ T, x₀ ∈ G.support := fun G hG => hIT G hG hx₀mem
  let jT : T → Fin N := fun G => j ⟨G.1, G.2, hxT G.1 G.2⟩
  have hJ : IdealSheafData.stalk I x₀ =
      Ideal.span (z '' ((Finset.univ.image jT : Finset (Fin N)) : Set (Fin N))) := by
    rw [hIst x₀ hx₀mem]
    refine iSup_eq_span_image z T _ _ (fun G hG => ⟨jT ⟨G, hG⟩,
      Finset.mem_image_of_mem _ (Finset.mem_univ _), hI ⟨G, hG, hxT G hG⟩⟩) fun i hi => ?_
    obtain ⟨G, -, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨G.1, G.2, hI ⟨G.1, G.2, hxT G.1 G.2⟩⟩
  have hzE : ∀ G : T, (blowUp I).ord (functionFieldMap (blowUpToBase I)
      (algebraMap _ Y.functionField (z (jT G)))) E.genericPoint = 1 := by
    intro G
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
    have hv := divisorialValuation_excE_param sY h hirr hc1' hz hJ
      (Finset.mem_image_of_mem jT (Finset.mem_univ G))
    refine ord_eq_of_divisorialValuation_eq E (fun h0 => ?_) hv
    rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hzΓ : ∀ (G : T) (Γ : Mori.PrimeDivisor Y), x₀ ∈ Γ.support →
      Y.ord (algebraMap _ Y.functionField (z (jT G))) Γ.genericPoint =
        if Γ = G.1 then 1 else 0 :=
    fun G Γ hΓ => ord_localEq Γ G.1 hΓ (hxT G.1 G.2) (hI ⟨G.1, G.2, hxT G.1 G.2⟩)
  -- the Hartogs relation along `E`
  let Gf : Option T → Y.functionField := fun i =>
    Option.elim i g fun G => algebraMap _ Y.functionField (z (jT G))
  let wt : Option T → ℝ := fun i => Option.elim i 1 fun _ => (m : ℝ)
  have hGf : ∀ i, Gf i ≠ 0 := by
    rintro (_ | G)
    · exact hg0
    · exact localEq_ne_zero G.1 (hxT G.1 G.2) (hI ⟨G.1, G.2, hxT G.1 G.2⟩)
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := blowUpToBase I) E Gf
    hGf wt fun Γ hΓ => by
      simp only [Fintype.sum_option, Gf, wt, Option.elim]
      rw [hgΓ Γ hΓ]
      simp_rw [hzΓ _ Γ hΓ]
      rw [hΔ Γ (hmemΓ Γ hΓ)]
      by_cases hΓT : Γ ∈ T
      · rw [Finset.sum_eq_single ⟨Γ, hΓT⟩]
        · simp [hΓT]
        · rintro G - hne
          have : Γ ≠ G.1 := fun h => hne (Subtype.ext h.symm)
          simp [this]
        · simp
      · rw [if_neg hΓT]
        simp only [Rat.cast_zero, mul_zero, neg_zero, mul_one, zero_add]
        refine Finset.sum_eq_zero fun G _ => ?_
        have : Γ ≠ G.1 := fun h => hΓT (h ▸ G.2)
        simp [this]
  simp only [Fintype.sum_option, Gf, wt, Option.elim, mul_one] at key
  simp_rw [hzE] at key
  simp only [Int.cast_one, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    nsmul_eq_mul] at key
  -- the numerical conclusion
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmain : (m : ℝ) * (a : ℝ) =
      ((blowUp I).ord (functionFieldMap (blowUpToBase I) g) E.genericPoint : ℝ) +
      (m : ℝ) * ((blowUp I).ord (algebraMap E.localRing (blowUp I).functionField h')
        E.genericPoint : ℝ) := by
    have h1 : (m : ℚ) * a = E.ordForm (pullbackRationalPluriForms sY (blowUpToBase I) τ) := hτa
    rw [hordτ] at h1
    have := congrArg (fun q : ℚ => (q : ℝ)) h1
    push_cast at this
    exact this
  rw [hord] at hmain
  push_cast at hmain
  have h2 : (m : ℝ) * (a : ℝ) = (m : ℝ) * (-1) := by linear_combination hmain + key
  have h3 := mul_left_cancel₀ hm'.ne' h2
  exact_mod_cast h3

end Stratum

end MMP.Fourfold

namespace MMP.Fourfold.ZeroPlaceExtraction

open MMP MMP.Mori MMP.Resolution MMP.Fourfold

open TopologicalSpace
open scoped WithZero

section GoodModel

open scoped Classical

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] (B : RDivisor X) (n : ℕ) (K : Divisor X) (ξ₀ : X)

/-- The invariants of the models of the extraction: `q : Y ⟶ X` is a proper birational morphism
from a smooth projective variety, total transforms of snc divisors containing `Supp B` are snc,
the reduced preimage of `⌊B⌋` is the crepant boundary of `(X, ⌊B⌋)`, and every prime divisor of
`Y` either lies over a prime divisor of `X` or lies over the centre `ξ₀`. -/
private structure IsGoodModel {Y : Scheme.{u}} (q : Y ⟶ X) : Prop where
  normal : IsNormalVariety k (q ≫ sX)
  bir : IsBirationalMorphism q
  proper : IsProper q
  smooth : IsSmoothScheme (q ≫ sX)
  proj : Mori.IsProjectiveVariety k (q ≫ sX)
  snc : ∀ S : Set X, (B.supp : Set X) ⊆ S → IsSNCClosedSubset sX S →
    IsSNCClosedSubset (q ≫ sX) (q ⁻¹' S)
  crep : ∀ G : Mori.PrimeDivisor Y, IsDiscrepancy sX n K (oneDivisor B) ⟨Y, q, normal, bir, G⟩
    (if q G.genericPoint ∈ oneLocus B then -1 else 0)
  exc : ∀ G : Mori.PrimeDivisor Y, q G.genericPoint = ξ₀ ∨ Order.coheight (q G.genericPoint) = 1

variable {sX B n K ξ₀}

/-- The identity is a good model. -/
private theorem isGoodModel_id [IsAlgClosed k] [CharZero k] (hX : Mori.IsProjectiveVariety k sX)
    (hXs : IsSmoothScheme sX) (hK : K.IsCanonicalDivisor sX n) :
    IsGoodModel sX B n K ξ₀ (𝟙 X) := by
  have hXv : IsNormalVariety k sX := ⟨hX.toIsVariety, inferInstance⟩
  have hn : IsNormalVariety k (𝟙 X ≫ sX) := by rwa [Category.id_comp]
  refine
    { normal := hn
      bir := isBirationalMorphism_of_isIso _
      proper := inferInstance
      smooth := by rwa [Category.id_comp]
      proj := by rwa [Category.id_comp]
      snc := fun S _ hS => by rwa [Category.id_comp]
      crep := fun G => ?_
      exc := fun G => Or.inr G.coheight_genericPoint }
  have hP : Mori.IsPair sX (oneDivisor B) :=
    ⟨hXv, n, K, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hXs _⟩
  obtain ⟨a, ha⟩ :=
    MMP.Positivity.IsPair.exists_isDiscrepancy hP hK (DivisorOver.ofPrimeDivisor k hXv G)
  have h1 := IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hXv ha
  change IsDiscrepancy sX n K (oneDivisor B) (DivisorOver.ofPrimeDivisor k hXv G) _
  convert ha using 1
  rw [h1, coeff_oneDivisor]
  change (if G.genericPoint ∈ oneLocus B then (-1 : ℚ) else 0) =
    -(if B.coeff G = 1 then (1 : ℚ) else 0)
  by_cases h : B.coeff G = 1
  · rw [if_pos ((genericPoint_mem_oneLocus_iff G).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((genericPoint_mem_oneLocus_iff G).mp h')), if_neg h, neg_zero]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Two divisors over `X` related by a birational morphism of their models over `X` matching the
generic points of the prime divisors have the same valuation. -/
private theorem valuation_eq_of_comp_eq (D₁ D₂ : DivisorOver k sX) (g : D₁.Y ⟶ D₂.Y)
    (hg : g ≫ D₂.f = D₁.f) (hbg : IsBirationalMorphism g)
    (hgen : g D₁.E.genericPoint = D₂.E.genericPoint) : D₁.valuation = D₂.valuation := by
  haveI := D₁.isIntegral
  haveI := D₂.isIntegral
  haveI := D₁.isNormal
  haveI := D₂.isNormal
  haveI := D₁.isLocallyNoetherian
  haveI := D₂.isLocallyNoetherian
  haveI := D₁.isDominant
  haveI := D₂.isDominant
  haveI : IsDominant g := hbg.isDominant
  let D' : DivisorOver k (D₂.f ≫ sX) :=
    ⟨D₁.Y, g, by rw [← Category.assoc, hg]; exact D₁.isNormalVariety, hbg, D₁.E⟩
  have h := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq D₂.isNormalVariety
    D' D₂.E hgen
  ext t
  have h' := congrArg (fun v => v (functionFieldMap D₂.f t)) h
  change D₁.E.divisorialValuation (functionFieldMap D₁.f t) =
    D₂.E.divisorialValuation (functionFieldMap D₂.f t)
  change D₁.E.divisorialValuation (functionFieldMap g (functionFieldMap D₂.f t)) =
    D₂.E.divisorialValuation (functionFieldMap (𝟙 _) (functionFieldMap D₂.f t)) at h'
  rw [MMP.Mori.functionFieldMap_id_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply] at h'
  have key : ∀ (φ : D₁.Y ⟶ X) [IsDominant φ], φ = D₁.f →
      functionFieldMap φ t = functionFieldMap D₁.f t := by
    rintro φ _ rfl; rfl
  rwa [key (g ≫ D₂.f) hg] at h'

/-- Good models are stable under precomposition with isomorphisms. -/
private theorem IsGoodModel.comp_iso [IsAlgClosed k] [CharZero k] (hXs : IsSmoothScheme sX)
    (hK : K.IsCanonicalDivisor sX n) {Y Y' : Scheme.{u}} {q : Y ⟶ X}
    (hq : IsGoodModel sX B n K ξ₀ q) (e : Y' ⟶ Y) [IsIso e] :
    IsGoodModel sX B n K ξ₀ (e ≫ q) := by
  haveI := hq.proper
  haveI : IsIntegral Y := hq.normal.1.toIsIntegral
  have hn : IsNormalVariety k ((e ≫ q) ≫ sX) := by
    rw [Category.assoc]; exact isNormalVariety_comp_iso hq.normal e
  haveI : IsIntegral Y' := hn.1.toIsIntegral
  have hb : IsBirationalMorphism (e ≫ q) :=
    isBirationalMorphism_comp (isBirationalMorphism_of_isIso e) hq.bir
  haveI : LocallyOfFiniteType (q ≫ sX) := hq.normal.1.toLocallyOfFiniteType
  haveI : QuasiCompact (q ≫ sX) := hq.normal.1.toQuasiCompact
  -- the prime divisor of `Y` below a prime divisor of `Y'`
  have hG₂ : ∀ G : Mori.PrimeDivisor Y', Order.coheight (e G.genericPoint) = 1 := fun G => by
    rw [Topology.IsOpenEmbedding.coheight_eq _ e.isOpenEmbedding, G.coheight_genericPoint]
  refine
    { normal := hn
      bir := hb
      proper := inferInstance
      smooth := ?_
      proj := ?_
      snc := fun S hS1 hS => ?_
      crep := fun G => ?_
      exc := fun G => ?_ }
  · rw [Category.assoc]
    haveI : Smooth (q ≫ sX) := (isSmoothScheme_iff _).mp hq.smooth
    exact (isSmoothScheme_iff _).mpr inferInstance
  · rw [Category.assoc]
    haveI : AlgebraicGeometry.IsVariety k (e ≫ q ≫ sX) := by
      have := hn.1; rwa [Category.assoc] at this
    obtain ⟨m, i, hi, hie⟩ := hq.proj.isProjective
    exact ⟨⟨m, e ≫ i, inferInstance, by rw [Category.assoc, hie]⟩⟩
  · rw [Category.assoc]
    exact (hq.snc S hS1 hS).preimage_of_isIso e
  · set G₂ := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ (hG₂ G)
    have hgen : e G.genericPoint = G₂.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm
    have hv := valuation_eq_of_comp_eq ⟨Y', e ≫ q, hn, hb, G⟩ ⟨Y, q, hq.normal, hq.bir, G₂⟩ e rfl
      (isBirationalMorphism_of_isIso e) hgen
    have hc := hq.crep G₂
    obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hc.isPair hK
      (⟨Y', e ≫ q, hn, hb, G⟩ : DivisorOver k sX)
    have hval := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq
      ⟨hc.isPair.1, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hXs _⟩ hv ha hc
    rw [hval] at ha
    change IsDiscrepancy sX n K (oneDivisor B) _
      (if q (e G.genericPoint) ∈ oneLocus B then -1 else 0)
    rwa [hgen]
  · change q (e G.genericPoint) = ξ₀ ∨ Order.coheight (q (e G.genericPoint)) = 1
    rw [show e G.genericPoint =
        (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ (hG₂ G)).genericPoint
      from (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm]
    exact hq.exc _

/-- The crepant boundary of `(X, ⌊B⌋)` on a good model, and the comparison of discrepancies. -/
private theorem IsGoodModel.exists_crepant [IsAlgClosed k] [CharZero k]
    (hXv : IsNormalVariety k sX) (hXs : IsSmoothScheme sX) (hBs : IsSNCClosedSubset sX B.supp)
    (hK : K.IsCanonicalDivisor sX n) {Y : Scheme.{u}} {q : Y ⟶ X}
    (hq : IsGoodModel sX B n K ξ₀ q) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] :
    haveI : IsDominant q := hq.bir.isDominant
    ∃ (KY : Divisor Y) (ΔY : QDivisor Y), KY.IsCanonicalDivisor (q ≫ sX) n ∧
      (∀ G, ΔY.coeff G = if q G.genericPoint ∈ oneLocus B then 1 else 0) ∧
      Mori.IsPair (q ≫ sX) ΔY ∧
      ∀ (D : DivisorOver k (q ≫ sX)) (E' : DivisorOver k sX),
        E'.valuation = D.valuation.comap (functionFieldMap q) → ∀ a : ℚ,
          (IsDiscrepancy (q ≫ sX) n KY ΔY D a ↔ IsDiscrepancy sX n K (oneDivisor B) E' a) := by
  haveI : IsDominant q := hq.bir.isDominant
  haveI := hq.proper
  haveI : LocallyOfFiniteType (q ≫ sX) := hq.normal.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety k (q ≫ sX) := hq.normal.1
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : CompactSpace Y := hq.normal.1.toQuasiCompact.compactSpace_of_compactSpace
  haveI : IsNoetherian Y := {}
  -- `Y` has dimension `n`
  have hdim : topologicalKrullDim Y = n := by
    rw [← hK.topologicalKrullDim_eq, ← toENat_trdeg_functionField (sX := q ≫ sX),
      ← toENat_trdeg_functionField (sX := sX),
      trdeg_functionField_eq_of_bijective _ q hq.bir.functionFieldMap_bijective]
  obtain ⟨KY, hKY⟩ :=
    MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (q ≫ sX) hq.smooth hdim
  -- the finitely many prime divisors over `⌊B⌋`
  have hfin : {G : Mori.PrimeDivisor Y | q G.genericPoint ∈ oneLocus B}.Finite :=
    (finite_setOf_support_subset (hq.snc _ le_rfl hBs)).subset fun G hG =>
      support_subset_preimage_supp q G hG
  set ΔY : QDivisor Y := ∑ G ∈ hfin.toFinset, Finsupp.single G 1 with hΔYdef
  have hΔY : ∀ G, ΔY.coeff G = if q G.genericPoint ∈ oneLocus B then 1 else 0 := by
    intro G
    rw [hΔYdef, DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    exact if_congr (Set.Finite.mem_toFinset _) rfl rfl
  have hP0 : Mori.IsPair sX (oneDivisor B) :=
    ⟨hXv, n, K, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hXs _⟩
  have hcb : IsCrepantBoundary sX n K (oneDivisor B) q hq.normal hq.bir ΔY := fun F => by
    have := hq.crep F
    convert this using 1
    rw [hΔY]
    split_ifs <;> simp
  obtain ⟨hPY, hiff⟩ := hP0.isDiscrepancy_iff_of_crepant q hq.normal hq.bir hK hKY (Or.inl hcb)
  exact ⟨KY, ΔY, hKY, hΔY, hPY, hiff⟩

/-- **The centre of a zero place on a good model.** If `E'` has discrepancy `-1` over
`(X, ⌊B⌋)` and is realized over the good model `Y` with centre `y` of codimension `≥ 2`, then the
components of the preimage of `Supp B` through `y` all lie over `⌊B⌋`, and there are exactly
`codim y` of them. -/
private theorem IsGoodModel.centre [IsAlgClosed k] [CharZero k] (hXs : IsSmoothScheme sX)
    (hBs : IsSNCClosedSubset sX B.supp) (hK : K.IsCanonicalDivisor sX n)
    {Y : Scheme.{u}} {q : Y ⟶ X} (hq : IsGoodModel sX B n K ξ₀ q)
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (D : DivisorOver k (q ≫ sX)) (hD2 : 2 ≤ Order.coheight (D.f D.E.genericPoint))
    (E' : DivisorOver k sX) (hE' : IsDiscrepancy sX n K (oneDivisor B) E' (-1))
    (hv : haveI : IsDominant q := hq.bir.isDominant
      E'.valuation = D.valuation.comap (functionFieldMap q)) :
    ∃ T : Finset (Mori.PrimeDivisor Y),
      (∀ G, G ∈ T ↔ ((G.support : Set Y) ⊆ q ⁻¹' B.supp ∧ D.f D.E.genericPoint ∈ G.support)) ∧
      (T.card : ℕ∞) = Order.coheight (D.f D.E.genericPoint) ∧
      ∀ G ∈ T, q G.genericPoint ∈ oneLocus B := by
  have hXv : IsNormalVariety k sX := hE'.1
  haveI : IsDominant q := hq.bir.isDominant
  haveI : LocallyOfFiniteType (q ≫ sX) := hq.normal.1.toLocallyOfFiniteType
  haveI : CompactSpace Y := hq.normal.1.toQuasiCompact.compactSpace_of_compactSpace
  haveI : IsNoetherian Y := {}
  obtain ⟨KY, ΔY, hKY, hΔY, -, hiff⟩ := hq.exists_crepant hXv hXs hBs hK
  have hD : IsDiscrepancy (q ≫ sX) n KY ΔY D (-1) := (hiff D E' hv (-1)).mpr hE'
  -- the components of the preimage of `Supp B`
  have hSY := hq.snc _ le_rfl hBs
  set S := (finite_setOf_support_subset hSY).toFinset with hSdef
  have hmemS : ∀ G, G ∈ S ↔ (G.support : Set Y) ⊆ q ⁻¹' B.supp := fun G =>
    Set.Finite.mem_toFinset _
  have hsnc := isSNC_sum_single_of_support_subset hq.smooth hSY S (fun P hP => (hmemS P).mp hP)
  have hΔS : ΔY.support ⊆ S := by
    intro G hG
    rw [hmemS]
    refine support_subset_preimage_supp q G ?_
    by_contra h
    rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, hΔY, if_neg h] at hG
    exact hG rfl
  have hcoeff : ∀ G ∈ S, ΔY.coeff G ≤ 1 := fun G _ => by
    rw [hΔY]
    split_ifs <;> norm_num
  have hDex : D.IsExceptional := (isExceptional_iff_two_le_coheight hq.normal D).mpr hD2
  obtain ⟨c, hc, -, hcard, hle⟩ :=
    le_isDiscrepancy_of_isSNC hq.normal hq.smooth hKY hΔS hsnc hcoeff D hDex hD
  set T := S.filter (fun G => D.f D.E.genericPoint ∈ G.support) with hT
  have hterm : ∀ G ∈ T, 0 ≤ 1 - ΔY.coeff G := fun G hG => by
    linarith [hcoeff G (Finset.mem_filter.mp hG).1]
  have hsum0 := Finset.sum_nonneg hterm
  have hct : (T.card : ℚ) ≤ c := by exact_mod_cast hcard
  refine ⟨T, fun G => by rw [hT, Finset.mem_filter, hmemS], ?_, fun G hG => ?_⟩
  · have h' : (c : ℚ) ≤ T.card := by linarith
    have : T.card = c := le_antisymm hcard (by exact_mod_cast h')
    rw [hc, this]
  · have hzero : ∑ G ∈ T, (1 - ΔY.coeff G) = 0 := by linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero G hG
    by_contra h
    rw [hΔY, if_neg h] at this
    norm_num at this

/-- **One stratum blow-up.** Blowing up the closure of a point `y ∈ q⁻¹(ξ₀)` of codimension `c ≥ 2`
through which exactly `c` components of the preimage of `Supp B` pass, all over `⌊B⌋`, gives a
good model, and the centre is a stratum of `q⁻¹(⌊B⌋)`. -/
private theorem IsGoodModel.blowUpToBase_comp [IsAlgClosed k] [CharZero k] (hXs : IsSmoothScheme sX)
    (hBs : IsSNCClosedSubset sX B.supp) (hK : K.IsCanonicalDivisor sX n)
    {Y : Scheme.{u}} {q : Y ⟶ X} (hq : IsGoodModel sX B n K ξ₀ q) (y : Y) (hqy : q y = ξ₀)
    (hy2 : 2 ≤ Order.coheight y) (T : Finset (Mori.PrimeDivisor Y))
    (hT : ∀ G, G ∈ T ↔ ((G.support : Set Y) ⊆ q ⁻¹' B.supp ∧ y ∈ G.support))
    (hTc : (T.card : ℕ∞) = Order.coheight y) (hT1 : ∀ G ∈ T, q G.genericPoint ∈ oneLocus B) :
    IsGoodModel sX B n K ξ₀
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {y})) ≫ q) ∧
      ∃ J : Set (Set Y), J.Nonempty ∧ J ⊆ componentsOf (q ⁻¹' oneLocus B) ∧
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {y})).support : Set Y) ∈
          componentsOf (⋂₀ J) := by
  -- the scheme `Y`
  haveI : IsIntegral Y := hq.normal.1.toIsIntegral
  haveI : IsNormal Y := hq.normal.2
  haveI : LocallyOfFiniteType (q ≫ sX) := hq.normal.1.toLocallyOfFiniteType
  haveI : QuasiCompact (q ≫ sX) := hq.normal.1.toQuasiCompact
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (q ≫ sX)
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (q ≫ sX)
  haveI : IsNoetherian Y := {}
  haveI : IsDominant q := hq.bir.isDominant
  haveI := hq.proper
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.card_empty, Nat.cast_zero] at hTc
    rw [← hTc] at hy2
    exact absurd hy2 (by decide)
  obtain ⟨G₀, hG₀⟩ := hTne
  have hXv : IsNormalVariety k sX := (hq.crep G₀).1
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  have hdim : topologicalKrullDim Y = n := by
    rw [← hK.topologicalKrullDim_eq, ← toENat_trdeg_functionField (sX := q ≫ sX),
      ← toENat_trdeg_functionField (sX := sX),
      trdeg_functionField_eq_of_bijective _ q hq.bir.functionFieldMap_bijective]
  have hSY := hq.snc _ le_rfl hBs
  have hTsub : ∀ G ∈ T, (G.support : Set Y) ⊆ q ⁻¹' B.supp := fun G hG => ((hT G).mp hG).1
  have hyT : ∀ G ∈ T, y ∈ G.support := fun G hG => ((hT G).mp hG).2
  have hsnc := isSNC_sum_single_of_support_subset hq.smooth hSY T hTsub
  have hc : Order.coheight y = T.card := hTc.symm
  -- the centre
  obtain ⟨hcomp, hZsm, hZst⟩ :=
    closure_singleton_mem_componentsOf_of_isSNC (q ≫ sX) hsnc hyT hc
  set Z := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {y}) with hZdef
  have hZsupp : (Z.support : Set Y) = closure {y} := by
    rw [hZdef, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]
  have hZst' : ∀ x ∈ Z.support, IdealSheafData.stalk Z x =
      ⨆ G ∈ T, IdealSheafData.stalk G.idealSheaf x := fun x hx => by
    rw [← SetLike.mem_coe, hZsupp] at hx
    exact hZst x hx
  have hZT : ∀ G ∈ T, (Z.support : Set Y) ⊆ G.support := fun G hG => by
    rw [hZsupp]
    exact closure_minimal (Set.singleton_subset_iff.mpr (hyT G hG))
      (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support G)
  have hirr : IsIrreducible (Z.support : Set Y) := hZsupp ▸ isIrreducible_singleton.closure
  have hcodim : codimension (⟨Z.support, hirr, Z.support.isClosed⟩ : IrreducibleCloseds Y) =
      T.card := by
    have heq : (⟨Z.support, hirr, Z.support.isClosed⟩ : IrreducibleCloseds Y) =
        IrreducibleCloseds.closureSingleton y := by
      ext1; exact hZsupp
    rw [heq, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton, hc]
  have hc2 : 2 ≤ T.card := by
    have := hy2
    rw [hc] at this
    exact_mod_cast this
  have hc1' : 1 ≤ codimension (⟨Z.support, hirr, Z.support.isClosed⟩ : IrreducibleCloseds Y) := by
    rw [hcodim]; exact_mod_cast (by omega : 1 ≤ T.card)
  have hsb : IsSmoothBlowup (q ≫ sX) Z := ⟨hq.smooth, hZsm⟩
  obtain ⟨hvar, hsmB, hproj, hbir, -, hprojV, -⟩ :=
    MMP.Threefold.Resolution.isVariety_smooth_blowUpToBase_divisorOfForm_pullbackRationalPluriForms
      (q ≫ sX) hq.normal.1 hdim Z hsb hirr hcodim.symm hc2
  set π := blowUpToBase Z with hπ
  haveI := MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension Z hirr hc1'
  haveI := MMP.Threefold.Resolution.isDominant_blowUpToBase Z hirr hc1'
  haveI : Smooth (π ≫ q ≫ sX) := hsmB
  haveI : IsLocallyNoetherian (AlgebraicGeometry.blowUp Z) :=
    isLocallyNoetherian_of_smooth (π ≫ q ≫ sX)
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI : IsNormal (AlgebraicGeometry.blowUp Z) := AlgebraicGeometry.isNormal_of_smooth (π ≫ q ≫ sX)
  haveI : IsProper π := hproj.isProper
  have hNπ : IsNormalVariety k (π ≫ q ≫ sX) := ⟨hvar, inferInstance⟩
  have hN : IsNormalVariety k ((π ≫ q) ≫ sX) := by rwa [Category.assoc]
  have hb : IsBirationalMorphism (π ≫ q) := isBirationalMorphism_comp hbir hq.bir
  -- the exceptional divisor
  set E := MMP.Fourfold.SNCWeight.StratumBlowup.excE (q ≫ sX) hsb hirr hc1' with hE
  have hEgen : π E.genericPoint = y := by
    have h1 := MMP.Fourfold.SNCWeight.BlowupCrepancy.closure_map_genericPoint_excE (q ≫ sX) hsb
      hirr hc1'
    rw [hZsupp] at h1
    exact (inseparable_iff_closure_eq.2 h1).eq
  have hoy : q y ∈ oneLocus B := support_subset_preimage_oneLocus q G₀ (hT1 G₀ hG₀) (hyT G₀ hG₀)
  refine ⟨⟨hN, hb, inferInstance, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Category.assoc]; exact (isSmoothScheme_iff _).mpr hsmB
  · rw [Category.assoc]; exact hprojV hq.proj
  · intro S hS1 hS
    have hS' := hq.snc S hS1 hS
    have hZS : (Z.support : Set Y) ⊆ q ⁻¹' S :=
      (hZT G₀ hG₀).trans ((hTsub G₀ hG₀).trans (Set.preimage_mono hS1))
    have hZ := hasSNCWith_of_stalk_eq hS' ⟨G₀, hG₀⟩
      (fun G hG => (hTsub G hG).trans (Set.preimage_mono hS1)) hZT hZst'
    have h := MMP.Resolution.isSNCClosedSubset_totalTransformStep (q ≫ sX) hq.smooth hS' hZ
    rw [MMP.Fourfold.SNCWeight.SNCBlowup.totalTransformStep_eq hS'.1 hZS] at h
    rw [Category.assoc]
    exact h
  · intro H
    by_cases hHE : H = E
    · subst hHE
      change IsDiscrepancy sX n K (oneDivisor B) _
        (if q (π E.genericPoint) ∈ oneLocus B then -1 else 0)
      rw [hEgen, if_pos hoy]
      obtain ⟨KY, ΔY, hKY, hΔY, hPY, hiff⟩ := hq.exists_crepant hXv hXs hBs hK
      refine (hiff ⟨AlgebraicGeometry.blowUp Z, π, hNπ, hbir, E⟩ _ ?_ (-1)).mp ?_
      · ext t
        change E.divisorialValuation (functionFieldMap (π ≫ q) t) =
          E.divisorialValuation (functionFieldMap π (functionFieldMap q t))
        rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
      · refine isDiscrepancy_excE_neg_one (q ≫ sX) hKY hPY hsb hirr hcodim.symm (by omega) hsnc
          hZT hZst' (fun Γ hΓ => ?_) hNπ hc1' hbir
        have hyΓ : y ∈ Γ.support := hΓ (hZsupp ▸ subset_closure rfl)
        rw [hΔY]
        by_cases hΓT : Γ ∈ T
        · rw [if_pos (hT1 Γ hΓT), if_pos hΓT]
        · rw [if_neg hΓT, if_neg]
          intro h1
          exact hΓT ((hT Γ).mpr ⟨support_subset_preimage_supp q Γ h1, hyΓ⟩)
    · set G₂ := MMP.Fourfold.SNCWeight.StratumBlowup.downPrime (q ≫ sX) hsb hirr hc1' hHE
      have hgen : π H.genericPoint = G₂.genericPoint :=
        (MMP.Fourfold.SNCWeight.StratumBlowup.genericPoint_downPrime _ _ _ _ hHE).symm
      have hv := valuation_eq_of_comp_eq ⟨AlgebraicGeometry.blowUp Z, π ≫ q, hN, hb, H⟩
        ⟨Y, q, hq.normal, hq.bir, G₂⟩ π rfl hbir hgen
      have hc' := hq.crep G₂
      obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hc'.isPair hK
        (⟨AlgebraicGeometry.blowUp Z, π ≫ q, hN, hb, H⟩ : DivisorOver k sX)
      have hval := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq
        ⟨hc'.isPair.1, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hXs _⟩ hv ha hc'
      rw [hval] at ha
      change IsDiscrepancy sX n K (oneDivisor B) _
        (if q (π H.genericPoint) ∈ oneLocus B then -1 else 0)
      rwa [hgen]
  · intro H
    change q (π H.genericPoint) = ξ₀ ∨ Order.coheight (q (π H.genericPoint)) = 1
    by_cases hHE : H = E
    · left; rw [hHE, hEgen, hqy]
    · rw [← MMP.Fourfold.SNCWeight.StratumBlowup.genericPoint_downPrime _ _ _ _ hHE]
      exact hq.exc _
  · refine ⟨(fun G : Mori.PrimeDivisor Y => (G.support : Set Y)) '' T, ⟨_, G₀, hG₀, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨G, hG, rfl⟩
      have hcomp' := support_mem_componentsOf hSY (hTsub G hG)
      exact ⟨⟨MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isIrreducible_support G,
        support_subset_preimage_oneLocus q G (hT1 G hG)⟩,
        fun W hW hle => hcomp'.2 ⟨hW.1, hW.2.trans (Set.preimage_mono (oneLocus_subset_supp B))⟩
          hle⟩
    · rw [hZsupp, Set.sInter_image]
      simpa using hcomp

/-- **The centre of a zero place of `⌊B⌋`.** If `E` has discrepancy `-1` over `(X, ⌊B⌋)` and its
centre has codimension at least two, then the centre lies on `⌊B⌋` and on no component of `B` with
coefficient in `(0, 1)`. -/
private theorem centre_mem_oneLocus [IsAlgClosed k] [CharZero k]
    (hX : Mori.IsProjectiveVariety k sX) (hXs : IsSmoothScheme sX)
    (hBs : IsSNCClosedSubset sX B.supp) (hK : K.IsCanonicalDivisor sX n)
    (E : MMP.Flips.ProperDivisorOver k sX) (hE2 : 2 ≤ Order.coheight (E.f E.E.genericPoint))
    (hE1 : IsDiscrepancy sX n K (oneDivisor B) E.toDivisorOver (-1)) :
    E.f E.E.genericPoint ∈ oneLocus B ∧
      ∀ P, B.coeff P ≠ 0 → B.coeff P < 1 → E.f E.E.genericPoint ∉ P.support := by
  let E₀ : DivisorOver k (𝟙 X ≫ sX) :=
    ⟨E.Y, E.f, by rw [Category.id_comp]; exact E.isNormalVariety, E.isBirationalMorphism, E.E⟩
  have hv₀ : E.toDivisorOver.valuation = E₀.valuation.comap (functionFieldMap (𝟙 X)) := by
    ext t
    change _ = E₀.valuation (functionFieldMap (𝟙 X) t)
    rw [MMP.Mori.functionFieldMap_id_apply]
    rfl
  obtain ⟨T, hT, hTc, hT1⟩ := (isGoodModel_id (ξ₀ := E.f E.E.genericPoint) hX hXs hK).centre
    hXs hBs hK E₀ hE2 E.toDivisorOver hE1 hv₀
  have h2 : (2 : ℕ∞) ≤ T.card := by rwa [hTc]
  obtain ⟨G, hG⟩ : T.Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast (show (0 : ℕ∞) < T.card from
      lt_of_lt_of_le (by norm_num) h2))
  refine ⟨support_subset_preimage_oneLocus (𝟙 X) G (hT1 G hG) ((hT G).mp hG).2,
    fun P hP0 hP1 hξP => hP1.ne ((genericPoint_mem_oneLocus_iff P).mp (hT1 P ((hT P).mpr
      ⟨fun x hx => DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, hP0, hx⟩, hξP⟩)))⟩

/-- On a good model, every exceptional prime divisor lies over the centre `ξ₀`. -/
private theorem IsGoodModel.apply_genericPoint_eq_of_isExceptional (hXv : IsNormalVariety k sX)
    {Y : Scheme.{u}} {q : Y ⟶ X} (hq : IsGoodModel sX B n K ξ₀ q) [IsLocallyNoetherian Y]
    [IsNormal Y] (F : Mori.PrimeDivisor Y)
    (hF : Mori.RationalMap.IsExceptional (X := Y) q.toRationalMap F) :
    q F.genericPoint = ξ₀ := by
  have := isSeparated_toTerminal hXv.1.toIsSeparated
  have h2 := (isExceptional_toRationalMap_iff_two_le_coheight q F).mp hF
  refine (hq.exc F).resolve_right fun h => ?_
  rw [h] at h2
  exact absurd h2 (by decide)

end GoodModel

/-! ### The Zariski sequence of a valuation ring -/

section Sequence

open IsLocalRing MMP.Mori.ZariskiSequence

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (x₀ : X)
  (R : Subring X.functionField)
  (hS : ∀ s : X.presheaf.stalk x₀, algebraMap (X.presheaf.stalk x₀) X.functionField s ∈ R)

/-- A stage of the Zariski sequence blowing up the whole scheme at each step, together with the
composite down to `X`. -/
private structure Stage where
  /-- The model. -/
  Y : Scheme.{u}
  /-- The morphism from `Spec R`. -/
  g : Spec (.of R) ⟶ Y
  /-- The composite down to `X`. -/
  q : Y ⟶ X
  good : Good Y g
  comm : g ≫ q = fromSpecOfStalkLE x₀ R hS

variable {x₀ R hS}

/-- The next stage: blow up the closure of the image of the closed point. -/
private noncomputable def Stage.next [ValuationRing R] (hR : ¬ IsField R) (P : Stage x₀ R hS) :
    Stage x₀ R hS where
  Y := blowUp (centerIdeal (P.g ≫ (Scheme.topIso P.Y).inv))
  g := (exists_lift hR _ (good_topIso_inv P.good)).choose
  q := blowUpToBase (centerIdeal (P.g ≫ (Scheme.topIso P.Y).inv)) ≫ (Scheme.topIso P.Y).hom ≫ P.q
  good := good_blowUp hR _ (good_topIso_inv P.good) _
    (exists_lift hR _ (good_topIso_inv P.good)).choose_spec
  comm := by
    rw [reassoc_of% (exists_lift hR _ (good_topIso_inv P.good)).choose_spec]
    simp [P.comm]

variable (x₀ R hS) in
/-- The stages of the Zariski sequence. -/
private noncomputable def stage [ValuationRing R] (hR : ¬ IsField R) : ℕ → Stage x₀ R hS
  | 0 => ⟨X, fromSpecOfStalkLE x₀ R hS, 𝟙 X, good_fromSpecOfStalkLE x₀ R hS, by simp⟩
  | i + 1 => (stage hR i).next hR

/-- The stages form a Zariski sequence. -/
private noncomputable def stageSeq [ValuationRing R] (hR : ¬ IsField R) :
    ZariskiSequence X (fromSpecOfStalkLE x₀ R hS) where
  obj i := (stage x₀ R hS hR i).Y
  mor i := (stage x₀ R hS hR i).g
  obj_zero := rfl
  mor_zero := Category.comp_id _
  U _ := ⊤
  morOpen i := (stage x₀ R hS hR i).g ≫ (Scheme.topIso _).inv
  morOpen_ι i := by simp
  obj_succ _ := rfl
  mor_succ_comp i := (exists_lift hR _ (good_topIso_inv (stage x₀ R hS hR i).good)).choose_spec

variable (x₀ R hS) in
/-- The morphism `Spec R ⟶ X` sends the closed point to `x₀`. -/
private theorem fromSpecOfStalkLE_closedPoint [IsLocalRing R]
    (hdom : IsLocalHom ((algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict R hS)) :
    fromSpecOfStalkLE x₀ R hS (closedPoint R) = x₀ := by
  haveI := hdom
  change X.fromSpecStalk x₀ (Spec.map (CommRingCat.ofHom
    ((algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict R hS)) (closedPoint R)) = x₀
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- `Spec R ⟶ Spec 𝒪_{X,x₀} ⟶ X` induces the inclusion `𝒪_{X,x₀} ⊆ R ⊆ k(X)` on stalks. -/
private theorem stalkClosedPointTo_eq_algebraMap [IsLocalRing R]
    (hdom : IsLocalHom ((algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict R hS))
    {f : Spec (.of R) ⟶ X} (hf : f = fromSpecOfStalkLE x₀ R hS)
    (c : X.presheaf.stalk (f (closedPoint R))) :
    ((Scheme.stalkClosedPointTo f c : R) : X.functionField) = algebraMap _ X.functionField c := by
  subst hf
  haveI := hdom
  obtain ⟨U, hU, a, rfl⟩ := X.presheaf.germ_exist c
  have hx₀ : x₀ ∈ U := by
    rwa [fromSpecOfStalkLE_closedPoint x₀ R hS hdom] at hU
  have key : (Scheme.stalkClosedPointTo (fromSpecOfStalkLE x₀ R hS)).hom
      (X.presheaf.germ U _ hU a) =
      (algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict R hS
        (X.presheaf.germ U x₀ hx₀ a) :=
    congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
      (CommRingCat.ofHom ((algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict R hS))
      U hU)
  refine (congrArg (fun r : R => (r : X.functionField)) key).trans ?_
  haveI : Nonempty U := ⟨⟨x₀, hx₀⟩⟩
  change algebraMap (X.presheaf.stalk x₀) X.functionField (X.presheaf.germ U x₀ _ a) = _
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, Scheme.algebraMap_germ_eq_germToFunctionField]

/-- **The stalk maps of a Zariski sequence are the function field maps.** For a morphism
`g : Spec R ⟶ Y` over `X` (compatibly with `Spec R ⟶ Spec 𝒪_{X,x₀} ⟶ X`), the induced map
`𝒪_{Y, g(m)} ⟶ R ⊆ k(X)` is the inverse of the function field map of `Y ⟶ X` on `𝒪_{Y, g(m)}`. -/
private theorem functionFieldMap_stalkClosedPointTo [ValuationRing R]
    (hdom : IsLocalHom ((algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict R hS))
    {Y : Scheme.{u}} [IsIntegral Y]
    (g : Spec (.of R) ⟶ Y) (q : Y ⟶ X) [IsDominant q]
    (hbij : Function.Surjective (functionFieldMap q))
    (hcomm : g ≫ q = fromSpecOfStalkLE x₀ R hS)
    (s : Y.presheaf.stalk (g (closedPoint R))) :
    functionFieldMap q ((Scheme.stalkClosedPointTo g s : R) : X.functionField) =
      algebraMap _ Y.functionField s := by
  -- `θ ∘ q^♯` is the inclusion `𝒪_{X, q y} ⊆ k(X)`
  have hθq : ∀ c : X.presheaf.stalk (q (g (closedPoint R))),
      ((Scheme.stalkClosedPointTo g ((q.stalkMap (g (closedPoint R))).hom c) : R) :
        X.functionField) = algebraMap _ X.functionField c := by
    intro c
    have h := stalkClosedPointTo_eq_algebraMap hdom hcomm c
    rwa [Scheme.stalkClosedPointTo_comp] at h
  -- write `ψ(s) = a / b` with `a, b ∈ 𝒪_{X, q y}`
  obtain ⟨t, ht⟩ := hbij (algebraMap _ Y.functionField s)
  suffices hts : ((Scheme.stalkClosedPointTo g s : R) : X.functionField) = t by
    rw [hts, ht]
  obtain ⟨a, b, hb, rfl⟩ :=
    IsFractionRing.div_surjective (A := X.presheaf.stalk (q (g (closedPoint R)))) t
  have hb0 : algebraMap (X.presheaf.stalk (q (g (closedPoint R)))) X.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  rw [map_div₀, MMP.Mori.functionFieldMap_algebraMap_stalk,
    MMP.Mori.functionFieldMap_algebraMap_stalk] at ht
  have hb' : algebraMap (Y.presheaf.stalk (g (closedPoint R))) Y.functionField
      ((q.stalkMap (g (closedPoint R))).hom b) ≠ 0 := by
    rw [← MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact (map_ne_zero _).mpr hb0
  have hrel : s * (q.stalkMap (g (closedPoint R))).hom b =
      (q.stalkMap (g (closedPoint R))).hom a := by
    apply IsFractionRing.injective (Y.presheaf.stalk (g (closedPoint R))) Y.functionField
    rw [map_mul, ← ht, div_mul_cancel₀ _ hb']
  have hrel' := congrArg (fun r => ((Scheme.stalkClosedPointTo g r : R) : X.functionField)) hrel
  simp only [map_mul, Subring.coe_mul, hθq] at hrel'
  rw [eq_div_iff hb0, hrel']

end Sequence

/-! ### Auxiliary statements about the boundary -/

section Boundary

open scoped Classical

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- The support of an snc divisor is an snc closed subset. -/
private theorem isSNCClosedSubset_supp {B : RDivisor X} (hB : B.IsSNC sX) :
    IsSNCClosedSubset sX B.supp := by
  have hTs := support_sum_single B.support
  have hT := (DivisorWithCoeffs.isSNC_iff_of_support_eq hTs).mpr hB
  have h := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC sX hT
  rw [hTs] at h
  rwa [DivisorWithCoeffs.coe_supp]

/-- The coefficient along `E` of the pull-back of a Cartier divisor `C` vanishes when `C` has
coefficient zero along every prime divisor through the centre of `E`. -/
private theorem coeff_isPullback_eq_zero_of_forall {D : DivisorOver k sX} {C : Divisor X}
    (hCc : C.IsCartier)
    {hC : ∀ Z : irreducibleComponents D.Y, D.f (componentGenericPoint D.Y Z) ∉ C.supp}
    {C' : Divisor D.Y} (h : haveI := D.isLocallyNoetherian; haveI := D.isNormal
      haveI := D.isDominant; C.IsPullback D.f hC C')
    (h0 : ∀ Γ : Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support → C.coeff Γ = 0) :
    C'.coeff D.E = 0 := by
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  set x := D.f D.E.genericPoint with hx
  obtain ⟨V, hV, φ, hφ⟩ := hCc x
  set Z0 := MMP.Mori.pointComponent x with hZ0
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : MMP.Mori.RationalFunctions X) with hgdef
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ D.E hV Z0]
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := D.f) D.E
    (fun _ : Unit => g) (fun _ => hg) (fun _ => 1) fun Γ hΓ => by
      have hZ : Γ.component = Z0 := Subsingleton.elim
        (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
      have e := hφ Γ ⟨x, hΓ, hV⟩
      rw [h0 Γ hΓ, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ] at e
      have e' : Scheme.ord g Γ.genericPoint = 0 := e.symm
      simp [e']
  simpa using key

/-- The coefficient along `E` of the pull-back of a prime divisor `P` through the centre of `E`
is at least one, when the local ring at the centre is regular. -/
private theorem one_le_coeff_isPullback_single {D : DivisorOver k sX} {P : Mori.PrimeDivisor X}
    (hreg : IsRegularLocalRing (X.presheaf.stalk (D.f D.E.genericPoint)))
    (hP : D.f D.E.genericPoint ∈ P.support)
    (hCc : Divisor.IsCartier (Finsupp.single P (1 : ℤ) : Divisor X))
    {hC : ∀ Z : irreducibleComponents D.Y,
      D.f (componentGenericPoint D.Y Z) ∉
        DivisorWithCoeffs.supp (Finsupp.single P (1 : ℤ) : Divisor X)}
    {C' : Divisor D.Y} (h : haveI := D.isLocallyNoetherian; haveI := D.isNormal
      haveI := D.isDominant; Divisor.IsPullback D.f (Finsupp.single P (1 : ℤ) : Divisor X) hC C') :
    1 ≤ C'.coeff D.E := by
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have := D.E.isDiscreteValuationRing_localRing
  set x := D.f D.E.genericPoint with hx
  obtain ⟨π, hπ0, -, hπord⟩ :=
    PrimeDivisor.exists_localEquation_of_isRegularLocalRing x hreg P hP
  obtain ⟨V, hV, φ, hφ⟩ := hCc x
  set Z0 := MMP.Mori.pointComponent x with hZ0
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : MMP.Mori.RationalFunctions X) with hgdef
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  have hπK : algebraMap (X.presheaf.stalk x) X.functionField π ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπ0)
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ D.E hV Z0]
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := D.f) D.E
    (fun b : Bool => if b then g else algebraMap _ X.functionField π)
    (by rintro (_ | _) <;> simp [hg, hπK]) (fun b => if b then 1 else -1) fun Γ hΓ => by
      have hZ : Γ.component = Z0 := Subsingleton.elim
        (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
      have e := hφ Γ ⟨x, hΓ, hV⟩
      rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ] at e
      simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
      rw [← e, hπord Γ hΓ]
      by_cases hΓP : Γ = P
      · subst hΓP
        simp [DivisorWithCoeffs.coeff_single_self]
      · simp [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hΓP), hΓP]
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false] at key
  have hgπ : D.Y.ord (functionFieldMap D.f g) D.E.genericPoint =
      D.Y.ord (functionFieldMap D.f (algebraMap _ X.functionField π)) D.E.genericPoint := by
    have : ((D.Y.ord (functionFieldMap D.f g) D.E.genericPoint : ℤ) : ℝ) =
        ((D.Y.ord (functionFieldMap D.f (algebraMap _ X.functionField π)) D.E.genericPoint :
          ℤ) : ℝ) := by linarith
    exact_mod_cast this
  rw [hgπ, MMP.Mori.functionFieldMap_algebraMap_stalk]
  -- `π` lies in the maximal ideal at `x`, hence its image in the maximal ideal along `E`
  have hπm : π ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hsp := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support P hP
    have e := hπord P hP
    rw [if_pos rfl, ← MMP.Mori.algebraMap_stalkSpecializes hsp π,
      P.ord_algebraMap_of_isUnit (hu.map _)] at e
    exact absurd e (by decide)
  have hmE : (D.f.stalkMap D.E.genericPoint).hom π ∈ IsLocalRing.maximalIdeal D.E.localRing :=
    (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp hπm (isUnit_of_map_unit _ _ hu)
  have hne : (D.f.stalkMap D.E.genericPoint).hom π ≠ 0 := by
    intro h0
    have e := MMP.Mori.functionFieldMap_algebraMap_stalk D.f D.E.genericPoint π
    rw [h0, map_zero] at e
    exact (map_ne_zero _).mpr hπK e
  exact_mod_cast le_ord_of_mem_pow D.E hne (N := 1) (by rwa [pow_one])

/-- **Changing the boundary by finitely many prime divisors.** On a smooth `X`, if `a` is the log
discrepancy of `E` over `(X, B)` and `B' = B + ∑_{P ∈ s} w_P P`, then
`a - ∑_{P ∈ s} w_P · coeff_E(f^*P)` is the log discrepancy of `E` over `(X, B')`. -/
private theorem exists_isLogDiscrepancy_of_coeff_eq (hsm : IsSmoothScheme sX) {n : ℕ}
    {B B' : RDivisor X} {D : DivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) (s : Finset (Mori.PrimeDivisor X))
    (w : Mori.PrimeDivisor X → ℝ) (hB' : ∀ Γ, B'.coeff Γ = B.coeff Γ + if Γ ∈ s then w Γ else 0) :
    ∃ e : Mori.PrimeDivisor X → ℤ,
      (∀ P ∈ s, ∃ hC C', (haveI := D.isLocallyNoetherian; haveI := D.isNormal
        haveI := D.isDominant
        Divisor.IsPullback D.f (Finsupp.single P (1 : ℤ) : Divisor X) hC C') ∧
          C'.coeff D.E = e P) ∧
      MMP.Intersection.IsLogDiscrepancy sX n B' D (a - ∑ P ∈ s, w P * e P) := by
  obtain ⟨hX, hf, ω, hω0, hK, m, r, C, C', hCc, hsum, hpb, rfl⟩ := h
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : CompactSpace D.Y := by
    have := D.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sX)
  have hP : ∀ P : Mori.PrimeDivisor X, ∃ P' : Divisor D.Y,
      Divisor.IsPullback D.f (Finsupp.single P (1 : ℤ) : Divisor X)
        (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f _) P' :=
    fun P => MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _)
  choose P' hP' using hP
  set σ := s.equivFin.symm with hσ
  have hsumσ : ∀ F : Mori.PrimeDivisor X → ℝ, ∑ i, F (σ i).1 = ∑ P ∈ s, F P := fun F => by
    rw [Equiv.sum_comp σ (fun x : s => F x.1), Finset.sum_coe_sort s F]
  refine ⟨fun P => (P' P).coeff D.E, fun P _ => ⟨_, P' P, hP' P, rfl⟩, ?_⟩
  refine ⟨hX, hf, ω, hω0, hK, m + s.card, Fin.append r (fun i => w (σ i).1),
    Fin.append C (fun i => Finsupp.single (σ i).1 1), Fin.append C' (fun i => P' (σ i).1),
    fun i => ?_, fun Γ => ?_, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hCc i
    · rw [Fin.append_right]; exact MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hB', ← add_assoc, hsum Γ,
      hsumσ (fun P => w P *
        ((DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℤ) : Divisor X) Γ : ℤ) : ℝ))]
    congr 1
    have : ∀ P, w P * ((DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℤ) : Divisor X) Γ : ℤ) : ℝ) =
        if P = Γ then w Γ else 0 := fun P => by
      by_cases hP : P = Γ
      · subst hP; simp [DivisorWithCoeffs.coeff_single_self]
      · simp [DivisorWithCoeffs.coeff_single_of_ne hP, hP]
    simp_rw [this]
    rw [Finset.sum_ite_eq']
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]; exact hpb i
    · simp only [Fin.append_right]
      exact ⟨MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f _, hP' (σ i).1⟩
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hsumσ (fun P => w P * ((P' P).coeff D.E : ℝ))]
    ring

/-- **A zero place of an snc boundary is a zero place of its reduced part.** If `a(E; X, B) = 0`
for an snc boundary `B` with coefficients in `[0, 1]`, then `a(E, X, ⌊B⌋) = -1`. -/
private theorem isDiscrepancy_oneDivisor [IsAlgClosed k] [CharZero k]
    (hXv : IsNormalVariety k sX) (hXs : IsSmoothScheme sX) {B : RDivisor X} (hB0 : 0 ≤ B)
    (hB1 : ∀ P, B.coeff P ≤ 1) (hB : B.IsSNC sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (E : MMP.Flips.ProperDivisorOver k sX)
    (hE : E.IsExceptional)
    (hE0 : MMP.Intersection.IsLogDiscrepancy sX n B E.toDivisorOver 0) :
    IsDiscrepancy sX n K (oneDivisor B) E.toDivisorOver (-1) := by
  have : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  have : Smooth sX := (isSmoothScheme_iff sX).mp hXs
  set D := E.toDivisorOver with hDdef
  set x := D.f D.E.genericPoint with hx
  have hreg := isRegularLocalRing_stalk_of_smooth_over_field sX x
  -- the fractional components, and those through the centre
  set Fr := B.support.filter (fun P => B.coeff P ≠ 1) with hFr
  set F := Fr.filter (fun P => x ∈ P.support) with hF
  -- `B₁ = ⌊B⌋ + ∑_{P ∈ F} P`
  set B₁ : QDivisor X := oneDivisor B + ∑ P ∈ F, Finsupp.single P 1 with hB₁
  have hB₁c : ∀ Γ, B₁.coeff Γ = if B.coeff Γ = 1 ∨ Γ ∈ F then 1 else 0 := by
    intro Γ
    rw [hB₁, DivisorWithCoeffs.coeff_add, coeff_oneDivisor, DivisorWithCoeffs.coeff_apply
      (∑ P ∈ F, _), Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    by_cases h1 : B.coeff Γ = 1
    · have : Γ ∉ F := fun h => (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2 h1
      simp [h1, this]
    · simp [h1]
  set w : Mori.PrimeDivisor X → ℝ := fun P => (if P ∈ F then 1 else 0) - B.coeff P with hw
  obtain ⟨e, he, hlog⟩ := exists_isLogDiscrepancy_of_coeff_eq hXs hE0 Fr w
    (B' := QDivisor.toRDivisor B₁) fun Γ => by
      rw [QDivisor.coeff_toRDivisor, hB₁c]
      by_cases h1 : B.coeff Γ = 1
      · have : Γ ∉ Fr := fun h => (Finset.mem_filter.mp h).2 h1
        have hΓF : Γ ∉ F := fun h => this (Finset.mem_filter.mp h).1
        simp [h1, this]
      · by_cases hz : B.coeff Γ = 0
        · have hFr' : Γ ∉ Fr := fun h =>
            (Finsupp.mem_support_iff.mp (Finset.mem_filter.mp h).1) hz
          have hF' : Γ ∉ F := fun h => hFr' (Finset.mem_filter.mp h).1
          simp [h1, hz, hFr', hF']
        · have hFr' : Γ ∈ Fr := Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hz, h1⟩
          by_cases hΓF : Γ ∈ F <;> simp [hw, h1, hFr', hΓF]
  -- the lower bound for `B₁`
  have hP1 : Mori.IsPair sX B₁ := ⟨hXv, n, K, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hXs _⟩
  obtain ⟨a₁, ha₁⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP1 hK D
  have hTs := support_sum_single B.support
  have hsnc := (DivisorWithCoeffs.isSNC_iff_of_support_eq hTs).mpr hB
  have hS : B₁.support ⊆ B.support := by
    intro Γ hΓ
    rw [Finsupp.mem_support_iff] at hΓ ⊢
    change B₁.coeff Γ ≠ 0 at hΓ
    change B.coeff Γ ≠ 0
    refine fun hz => hΓ ?_
    rw [hB₁c, if_neg]
    rintro (h | h)
    · exact zero_ne_one (hz ▸ h)
    · exact (Finsupp.mem_support_iff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1) hz
  have hcoeff : ∀ Γ ∈ B.support, B₁.coeff Γ ≤ 1 := fun Γ _ => by
    rw [hB₁c]
    split_ifs <;> norm_num
  have hDex : D.IsExceptional := (isExceptional_iff_two_le_coheight hXv D).mpr
    ((properDivisorOver_isExceptional_iff hK.topologicalKrullDim_eq E).mp hE)
  obtain ⟨c, -, -, hcard, hle⟩ := le_isDiscrepancy_of_isSNC hXv hXs hK hS hsnc hcoeff D hDex ha₁
  have hlow : (-1 : ℚ) ≤ a₁ := by
    have h1 : 0 ≤ ∑ G ∈ B.support.filter (fun G => x ∈ G.support), (1 - B₁.coeff G) :=
      Finset.sum_nonneg fun G hG => by
        have := hcoeff G (Finset.mem_filter.mp hG).1
        linarith
    have h2 : ((B.support.filter (fun G => x ∈ G.support)).card : ℚ) ≤ c := by
      exact_mod_cast hcard
    linarith
  have hv₁ := ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy ha₁ _).mp hlog).2
  -- the terms of the correction
  have ht : ∀ P ∈ Fr, (x ∈ P.support → 0 < w P * (e P : ℝ)) ∧
      (x ∉ P.support → w P * (e P : ℝ) = 0) := by
    intro P hP
    obtain ⟨hC, C', hpb, hce⟩ := he P hP
    have hPlt : B.coeff P < 1 := lt_of_le_of_ne (hB1 P) (Finset.mem_filter.mp hP).2
    refine ⟨fun hxP => ?_, fun hxP => ?_⟩
    · have hPF : P ∈ F := Finset.mem_filter.mpr ⟨hP, hxP⟩
      have he1 := one_le_coeff_isPullback_single hreg hxP
        (MMP.Fourfold.isCartier_of_isSmoothScheme hXs _) hpb
      rw [hce] at he1
      have : (1 : ℝ) ≤ e P := by exact_mod_cast he1
      simp only [hw, if_pos hPF]
      nlinarith
    · have h0 := coeff_isPullback_eq_zero_of_forall
        (MMP.Fourfold.isCartier_of_isSmoothScheme hXs _) hpb fun Γ hΓ =>
          DivisorWithCoeffs.coeff_single_of_ne (fun h => hxP (by rwa [h])) 1
      rw [hce] at h0
      simp [h0]
  have hnn : ∀ P ∈ Fr, 0 ≤ w P * (e P : ℝ) := fun P hP => by
    by_cases hxP : x ∈ P.support
    · exact ((ht P hP).1 hxP).le
    · exact ((ht P hP).2 hxP).ge
  have hsum0 : ∑ P ∈ Fr, w P * (e P : ℝ) = 0 := by
    have := Finset.sum_nonneg hnn
    have : ((-1 : ℚ) : ℝ) ≤ a₁ := by exact_mod_cast hlow
    push_cast at this
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0
  have hFe : F = ∅ := Finset.filter_eq_empty_iff.mpr fun P hP hxP =>
    ((ht P hP).1 hxP).ne' (hzero P hP)
  have hB₁eq : B₁ = oneDivisor B := by rw [hB₁, hFe, Finset.sum_empty, add_zero]
  rw [hB₁eq] at ha₁
  have ha : (a₁ : ℝ) = -1 := by linarith
  rwa [show a₁ = -1 by exact_mod_cast ha] at ha₁

/-- A divisor with discrepancy `-1` over `⌊B⌋` whose centre lies on no component of `B` with
coefficient in `(0, 1)` has log discrepancy `0` over `B`. -/
private theorem isLogDiscrepancy_of_isDiscrepancy_oneDivisor [IsAlgClosed k] [CharZero k]
    (hXv : IsNormalVariety k sX) (hXs : IsSmoothScheme sX) {B : RDivisor X}
    (hB1 : ∀ P, B.coeff P ≤ 1) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (D : DivisorOver k sX) (hDp : IsProper D.f)
    (hD : IsDiscrepancy sX n K (oneDivisor B) D (-1))
    (hP : ∀ P, B.coeff P ≠ 0 → B.coeff P < 1 → D.f D.E.genericPoint ∉ P.support) :
    MMP.Intersection.IsLogDiscrepancy sX n B D 0 := by
  have : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  have h0 : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor (oneDivisor B)) D 0 := by
    have := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hD hDp
    convert this using 1
    push_cast
    ring
  set Fr := B.support.filter (fun P => B.coeff P ≠ 1) with hFr
  obtain ⟨e, he, hlog⟩ := exists_isLogDiscrepancy_of_coeff_eq hXs h0 Fr B.coeff
    (B' := B) fun Γ => by
      rw [QDivisor.coeff_toRDivisor, coeff_oneDivisor]
      by_cases h1 : B.coeff Γ = 1
      · have : Γ ∉ Fr := fun h => (Finset.mem_filter.mp h).2 h1
        simp [h1, this]
      · by_cases hz : B.coeff Γ = 0
        · have : Γ ∉ Fr := fun h => (Finsupp.mem_support_iff.mp (Finset.mem_filter.mp h).1) hz
          simp [h1, hz, this]
        · have : Γ ∈ Fr := Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hz, h1⟩
          simp [h1, this]
  have hsum : ∑ P ∈ Fr, B.coeff P * (e P : ℝ) = 0 := Finset.sum_eq_zero fun P hPm => by
    obtain ⟨hPs, hP1⟩ := Finset.mem_filter.mp hPm
    have hP0 : B.coeff P ≠ 0 := Finsupp.mem_support_iff.mp hPs
    obtain ⟨hC, C', hpb, hce⟩ := he P hPm
    have h0 := coeff_isPullback_eq_zero_of_forall
      (MMP.Fourfold.isCartier_of_isSmoothScheme hXs _) hpb fun Γ hΓ =>
        DivisorWithCoeffs.coeff_single_of_ne
          (fun h => hP P hP0 (lt_of_le_of_ne (hB1 P) hP1) (by rwa [h])) 1
    rw [← hce, h0]
    simp
  rw [hsum, sub_zero] at hlog
  exact hlog

end Boundary

end MMP.Fourfold.ZeroPlaceExtraction

namespace MMP.Fourfold

open MMP.Mori MMP.Resolution
open MMP.Fourfold.ZeroPlaceExtraction
open TopologicalSpace
open scoped WithZero

/-! ### Realizing the valuation on the models -/

section Realize

open IsLocalRing MMP.Mori.ZariskiSequence

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- **The divisor `E` over the models of the Zariski sequence.** Let `R` be the valuation ring of
`ord_E` and `g : Spec R ⟶ Y` a morphism over `X` to a normal proper birational model. Then `ord_E`
is realized by a proper divisor over `Y` whose centre is the image of the closed point. -/
theorem exists_properDivisorOver_comap_valuation_eq (hXv : IsNormalVariety k sX)
    (E : MMP.Flips.ProperDivisorOver k sX) {x₀ : X} (R : Subring X.functionField)
    [ValuationRing R] (hRv : ∀ g, g ∈ R ↔ E.valuation g ≤ 1)
    (hS : ∀ s : X.presheaf.stalk x₀, algebraMap (X.presheaf.stalk x₀) X.functionField s ∈ R)
    {Y : Scheme.{u}} (q : Y ⟶ X) (hY : IsNormalVariety k (q ≫ sX)) (hq : IsBirationalMorphism q)
    [IsProper q] (hdom : IsLocalHom
      ((algebraMap (X.presheaf.stalk x₀) X.functionField).codRestrict R hS))
    (g : Spec (.of R) ⟶ Y) (hcomm : g ≫ q = fromSpecOfStalkLE x₀ R hS) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : IsDominant q := hq.isDominant
    ∃ D : MMP.Flips.ProperDivisorOver k (q ≫ sX),
      D.f D.E.genericPoint = g (closedPoint _) ∧
        E.valuation = D.valuation.comap (functionFieldMap q) := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsDominant q := hq.isDominant
  haveI : IsNormal Y := hY.2
  haveI : AlgebraicGeometry.IsVariety k (q ≫ sX) := hY.1
  have hbij := hq.functionFieldMap_bijective
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective _ hbij
  let ξ : Valuation Y.functionField ℤᵐ⁰ :=
    E.valuation.comap (e.symm : Y.functionField →+* X.functionField)
  have hξ : ξ.comap (functionFieldMap q) = E.valuation := by
    ext t
    change E.valuation (e.symm (e t)) = E.valuation t
    rw [e.symm_apply_apply]
  -- `ξ` is a divisor of `k(Y)`
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (q ≫ sX) ξ := by
    have := E.isIntegral
    have := E.isNormal
    have := E.isLocallyNoetherian
    have := E.isDominant
    refine ⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E, ?_⟩
    let := MMP.Mori.functionFieldAlgebra sX
    let := MMP.Mori.functionFieldAlgebra (q ≫ sX)
    let := MMP.Mori.functionFieldAlgebra (E.f ≫ sX)
    let eP := MMP.Mori.functionFieldAlgEquiv sX q hbij
    let eY :=
      MMP.Mori.functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eP.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbij.2 t
    have h1 : eP.symm (functionFieldMap q s) = s := eP.symm_apply_apply s
    change E.valuation (e.symm (e s)) =
      E.E.divisorialValuation (eY (eP.symm (functionFieldMap q s)))
    rw [h1, e.symm_apply_apply]
    rfl
  -- `ξ` dominates the local ring at the image of the closed point
  have hF := functionFieldMap_stalkClosedPointTo hdom g q hbij.2 hcomm
  have hθ : ∀ a : Y.presheaf.stalk (g (closedPoint R)),
      e.symm (algebraMap _ Y.functionField a) =
        ((Scheme.stalkClosedPointTo g a : R) : X.functionField) := fun a => by
    rw [RingEquiv.symm_apply_eq]
    exact (hF a).symm
  have hle : ∀ a : Y.presheaf.stalk (g (closedPoint R)),
      ξ (algebraMap _ Y.functionField a) ≤ 1 := fun a => by
    change E.valuation (e.symm _) ≤ 1
    rw [hθ]
    exact (hRv _).1 (Scheme.stalkClosedPointTo g a).2
  have hlt : ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (g (closedPoint R))),
      ξ (algebraMap _ Y.functionField a) < 1 := fun a ha => by
    change E.valuation (e.symm _) < 1
    rw [hθ]
    set r := Scheme.stalkClosedPointTo g a
    have hr : r ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
        (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_map_unit _ _ hu)
    refine lt_of_le_of_ne ((hRv _).1 r.2) fun h1 => ?_
    refine (IsLocalRing.mem_maximalIdeal _).mp hr ?_
    have hr0 : (r : X.functionField) ≠ 0 := fun h0 => by
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    have hinv : (r : X.functionField)⁻¹ ∈ R := (hRv _).2 (by rw [map_inv₀, h1, inv_one])
    exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : R) (Subtype.ext (mul_inv_cancel₀ hr0))
  obtain ⟨D, -, hDv, hDx⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (q ≫ sX) hdiv _ hle hlt
  exact ⟨D, hDx, by rw [hDv, hξ]⟩

end Realize

/-- **Extracting an snc zero place by stratum blow-ups.** Let `X` be a smooth projective variety
over an algebraically closed field `k` of characteristic zero, `B` an effective snc boundary on
`X` with coefficient-one locus `D₀`, and `E` an exceptional divisor over `X` with
`a(E; X, B) = 0`. Then there is a smooth projective `W` with a composite `p : W ⟶ X` of blow-ups
of strata of the coefficient-one boundary, each centre containing the centre of `E` on the model
blown up, and a prime `E_W` of `W` with `ord_{E_W} = ord_E`, such that every `p`-exceptional prime
has log discrepancy zero over `(X, B)`, `p⁻¹(S)` is snc for every snc closed `S ⊇ Supp B`, and
`p^*A` vanishes at every `p`-exceptional prime for every effective `ℚ`-Cartier `A ≤ B` with no
component in `⌊B⌋`. -/
@[mmp "lem_fourfold_snc_zero_place_stratum_extraction"]
public theorem exists_stratumBlowups_valuation_eq_of_isLogDiscrepancy_eq_zero {k : Type u}
    [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (hX : Mori.IsProjectiveVariety k sX) (hXs : IsSmoothScheme sX)
    (B : RDivisor X) (hB0 : 0 ≤ B) (hB1 : ∀ P, B.coeff P ≤ 1) (hB : B.IsSNC sX)
    (E : MMP.Flips.ProperDivisorOver k sX) (hE : E.IsExceptional) (n : ℕ)
    (hE0 : MMP.Intersection.IsLogDiscrepancy sX n B E.toDivisorOver 0) :
    ∃ (W : Scheme.{u}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (_ : CompactSpace W) (p : W ⟶ X) (hN : IsNormalVariety k (p ≫ sX))
      (hb : IsBirationalMorphism p) (EW : Mori.PrimeDivisor W),
      -- `W` is smooth projective
      Mori.IsProjectiveVariety k (p ≫ sX) ∧ IsSmoothScheme (p ≫ sX) ∧
      -- `p` is a composite of stratum blow-ups whose centres contain the centre of `E`
      (∀ P : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Y → Prop, (∀ x : X, P (𝟙 X) x) →
        (∀ {Y Y' : Scheme.{u}} (e : Y' ⟶ Y) [IsIso e] (q : Y ⟶ X) (y : Y'), P q (e y) →
          P (e ≫ q) y) →
        (∀ {Y : Scheme.{u}} (q : Y ⟶ X) (Z : Y.IdealSheafData) (y : blowUp Z),
          P q (blowUpToBase Z y) →
          (∃ J : Set (Set Y), J.Nonempty ∧
            J ⊆ componentsOf
              (q ⁻¹' {x | ∃ D : Mori.PrimeDivisor X, B.coeff D = 1 ∧ x ∈ D.support}) ∧
            (Z.support : Set Y) ∈ componentsOf (⋂₀ J)) →
          Z = Scheme.IdealSheafData.vanishingIdeal Z.support → blowUpToBase Z y ∈ Z.support →
          P (blowUpToBase Z ≫ q) y) → P p EW.genericPoint) ∧
      -- `E` appears on `W` as `E_W`
      (⟨W, p, hN, hb, EW⟩ : DivisorOver k sX).valuation = E.valuation ∧
      -- every `p`-exceptional prime has log discrepancy zero
      (∀ F : Mori.PrimeDivisor W, Mori.RationalMap.IsExceptional (X := W) p.toRationalMap F →
        MMP.Intersection.IsLogDiscrepancy sX n B ⟨W, p, hN, hb, F⟩ 0) ∧
      -- total transforms of snc divisors containing `Supp B` stay snc
      (∀ S : Set X, (B.supp : Set X) ⊆ S → IsSNCClosedSubset sX S →
        IsSNCClosedSubset (p ≫ sX) (p ⁻¹' S)) ∧
      -- `ord_F A = 0` at every `p`-exceptional prime
      ∀ A : QDivisor X, 0 ≤ A → A.toRDivisor ≤ B → A.IsQCartier →
        (∀ P, A.coeff P ≠ 0 → B.coeff P < 1) →
        ∀ (hA : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ A.supp)
          (A' : QDivisor W), QDivisor.IsPullback p A hA A' →
          ∀ F : Mori.PrimeDivisor W, Mori.RationalMap.IsExceptional (X := W) p.toRationalMap F →
            A'.coeff F = 0 := by
  classical
  have hXv : IsNormalVariety k sX := ⟨hX.toIsVariety, inferInstance⟩
  obtain ⟨K, hK⟩ : ∃ K : Divisor X, K.IsCanonicalDivisor sX n := by
    obtain ⟨-, -, ω, -, ⟨K, hK, -⟩, -⟩ := hE0
    exact ⟨K, hK⟩
  have hBs := isSNCClosedSubset_supp hB
  have hE1 := isDiscrepancy_oneDivisor hXv hXs hB0 hB1 hB hK E hE hE0
  set ξ₀ := E.f E.E.genericPoint with hξ₀
  have hE2 : 2 ≤ Order.coheight ξ₀ := by
    haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
    exact (properDivisorOver_isExceptional_iff hK.topologicalKrullDim_eq E).mp hE
  have hG0 : IsGoodModel sX B n K ξ₀ (𝟙 X) := isGoodModel_id hX hXs hK
  -- the centre of `E` on `X` is a stratum of `⌊B⌋` off the other components of `B`
  obtain ⟨hξ₀1, hξ₀P⟩ := centre_mem_oneLocus hX hXs hBs hK E hE2 hE1
  -- the valuation ring of `E`
  set v := E.valuation with hv
  have hv1 := MMP.Positivity.DivisorOver.exists_valuation_eq_exp_neg_one E.toDivisorOver
  haveI := isRankOneDiscrete_of_exists_eq_exp_neg_one v hv1
  set R : Subring X.functionField := v.valuationSubring.toSubring with hRdef
  haveI : IsDiscreteValuationRing R := inferInstanceAs (IsDiscreteValuationRing v.valuationSubring)
  haveI : ValuationRing R := inferInstanceAs (ValuationRing v.valuationSubring)
  have hRf : ¬ IsField R := IsDiscreteValuationRing.not_isField R
  have h1 := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one E.toDivisorOver ξ₀ rfl
  have h2 := MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one E.toDivisorOver ξ₀ rfl
  have hS : ∀ s : X.presheaf.stalk ξ₀, algebraMap _ X.functionField s ∈ R :=
    fun s => (v.mem_valuationSubring_iff _).2 (h1 s)
  have hdom : IsLocalHom ((algebraMap (X.presheaf.stalk ξ₀) X.functionField).codRestrict R hS) :=
    isLocalHom_codRestrict_valuationSubring v _ h1 h2
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  haveI : IsSeparated (X ↘ Spec (.of k)) := hXv.1.toIsSeparated
  haveI : LocallyOfFiniteType (X ↘ Spec (.of k)) := hXv.1.toLocallyOfFiniteType
  haveI : QuasiCompact (X ↘ Spec (.of k)) := hXv.1.toQuasiCompact
  have htrdeg := trdeg_residueField_add_one_eq (X := X) hXv.1 E ξ₀ rfl R
    v.mem_valuationSubring_iff hS
  obtain ⟨n₀, hn₀⟩ := MMP.Mori.ZariskiSequence.exists_isIso_stalkClosedPointTo (k := k) ξ₀ R hS
    hdom htrdeg (stageSeq hRf)
  -- the stages and the centres
  set st := stage ξ₀ R hS hRf with hst
  set y : ∀ i, (st i).Y := fun i => (st i).g (IsLocalRing.closedPoint R) with hy
  have hfrom : fromSpecOfStalkLE ξ₀ R hS (IsLocalRing.closedPoint R) = ξ₀ :=
    fromSpecOfStalkLE_closedPoint ξ₀ R hS hdom
  have hqy : ∀ i, (st i).q (y i) = ξ₀ := fun i =>
    (congrArg (fun f : Spec (.of R) ⟶ X => f (IsLocalRing.closedPoint R)) (st i).comm).trans hfrom
  have hex : ∃ i, Order.coheight (y i) = 1 := by
    refine ⟨n₀, ?_⟩
    haveI : IsIso (Scheme.stalkClosedPointTo (st n₀).g) := hn₀
    have hdim : ringKrullDim ((st n₀).Y.presheaf.stalk (y n₀)) = 1 := by
      rw [ringKrullDim_eq_of_ringEquiv
        (asIso (Scheme.stalkClosedPointTo (st n₀).g)).commRingCatIsoToRingEquiv]
      exact IsDiscreteValuationRing.ringKrullDim_eq_one _
    rw [ringKrullDim_stalk_eq_coheight] at hdim
    exact_mod_cast hdim
  set N := Nat.find hex with hNdef
  have hN : Order.coheight (y N) = 1 := Nat.find_spec hex
  have hlt : ∀ i < N, 2 ≤ Order.coheight (y i) := by
    intro i hi
    have h1 : Order.coheight (y i) ≠ 1 := Nat.find_min hex hi
    obtain ⟨hYi, -, ha, hb⟩ := (st i).good
    have hng' : ¬ IsGenericPoint (y i) Set.univ := not_isGenericPoint_closedPoint _ hRf ha hb.2
    have h0 : Order.coheight (y i) ≠ 0 := by
      intro h0
      apply hng'
      have hsp : genericPoint (st i).Y ⤳ y i := (genericPoint_spec _).specializes trivial
      have hsp' : y i ⤳ genericPoint (st i).Y := (Order.coheight_eq_zero.1 h0) hsp
      have heq : y i = genericPoint (st i).Y := (hsp'.antisymm hsp).eq
      rw [heq]
      exact genericPoint_spec _
    generalize Order.coheight (y i) = c at h0 h1 ⊢
    induction c using ENat.recTopCoe with
    | top => exact le_top
    | coe c =>
      norm_cast at h0 h1 ⊢
      omega
  -- the induction along the Zariski sequence
  have key : ∀ i ≤ N, IsGoodModel sX B n K ξ₀ (st i).q ∧ IsStratumReached B (st i).q (y i) := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨hG0, fun P h0 _ _ => h0 _⟩
    | succ i ih =>
      intro hi
      obtain ⟨hGi, hRi⟩ := ih (by omega)
      have hiN : i < N := by omega
      haveI : IsIntegral (st i).Y := hGi.normal.1.toIsIntegral
      set e := (Scheme.topIso (st i).Y).hom with he
      have hG' := hGi.comp_iso hXs hK e
      haveI : IsIntegral (⊤ : (st i).Y.Opens).toScheme := hG'.normal.1.toIsIntegral
      haveI : IsNormal (⊤ : (st i).Y.Opens).toScheme := hG'.normal.2
      haveI : LocallyOfFiniteType (e ≫ (st i).q ≫ sX) := by
        rw [← Category.assoc]
        exact hG'.normal.1.toLocallyOfFiniteType
      haveI : IsLocallyNoetherian (⊤ : (st i).Y.Opens).toScheme :=
        LocallyOfFiniteType.isLocallyNoetherian (e ≫ (st i).q ≫ sX)
      haveI : IsProper (e ≫ (st i).q) := hG'.proper
      set g' := (st i).g ≫ (Scheme.topIso (st i).Y).inv with hg'
      have hcomm' : g' ≫ e ≫ (st i).q = fromSpecOfStalkLE ξ₀ R hS := by
        rw [hg', he, Category.assoc, Iso.inv_hom_id_assoc, (st i).comm]
      set y' := g' (IsLocalRing.closedPoint R) with hy'
      have hey : e y' = y i := by
        change ((st i).g ≫ (Scheme.topIso (st i).Y).inv ≫ (Scheme.topIso (st i).Y).hom)
          (IsLocalRing.closedPoint R) = (st i).g (IsLocalRing.closedPoint R)
        rw [Iso.inv_hom_id, Category.comp_id]
      have hcoh' : 2 ≤ Order.coheight y' := by
        rw [← Topology.IsOpenEmbedding.coheight_eq (x := y') _ e.isOpenEmbedding, hey]
        exact hlt i hiN
      obtain ⟨D, hDy, hDv⟩ := exists_properDivisorOver_comap_valuation_eq hXv E R
        v.mem_valuationSubring_iff hS (e ≫ (st i).q) hG'.normal hG'.bir hdom g'
        hcomm'
      obtain ⟨T, hT, hTc, hT1⟩ := hG'.centre hXs hBs hK D.toDivisorOver (hDy ▸ hcoh')
        E.toDivisorOver hE1 hDv
      rw [hDy] at hT hTc
      have hqy' : (e ≫ (st i).q) y' = ξ₀ := by rw [Scheme.Hom.comp_apply, hey, hqy]
      obtain ⟨hGn, J, hJ⟩ := hG'.blowUpToBase_comp hXs hBs hK y' hqy' hcoh' T hT hTc hT1
      refine ⟨hGn, ?_⟩
      intro P h0 hiso hbl
      have hPi := hRi P h0 hiso hbl
      have hP' : P (e ≫ (st i).q) y' := hiso e (st i).q y' (by rwa [hey])
      have hlift := (exists_lift hRf _ (good_topIso_inv (st i).good)).choose_spec
      set y₁ := (exists_lift hRf _ (good_topIso_inv (st i).good)).choose
        (IsLocalRing.closedPoint R) with hy₁
      have hbase : blowUpToBase (centerIdeal g') y₁ = y' := by
        change ((exists_lift hRf _ (good_topIso_inv (st i).good)).choose ≫
          blowUpToBase (centerIdeal ((st i).g ≫ (Scheme.topIso (st i).Y).inv)))
            (IsLocalRing.closedPoint R) = y'
        rw [hlift]
      have hsupp : (centerIdeal g').support = Closeds.closure {y'} :=
        Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
      exact hbl (e ≫ (st i).q) (centerIdeal g') y₁ (by rwa [hbase]) ⟨J, hJ⟩
        (by rw [hsupp]; rfl)
        (by
          rw [hbase, hsupp, ← SetLike.mem_coe, Closeds.coe_closure]
          exact subset_closure rfl)
  obtain ⟨hGN, hRN⟩ := key N le_rfl
  haveI : IsIntegral (st N).Y := hGN.normal.1.toIsIntegral
  haveI : IsNormal (st N).Y := hGN.normal.2
  haveI : LocallyOfFiniteType ((st N).q ≫ sX) := hGN.normal.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (st N).Y := LocallyOfFiniteType.isLocallyNoetherian ((st N).q ≫ sX)
  haveI : CompactSpace (st N).Y := hGN.normal.1.toQuasiCompact.compactSpace_of_compactSpace
  haveI : IsProper (st N).q := hGN.proper
  haveI : IsDominant (st N).q := hGN.bir.isDominant
  set EW : Mori.PrimeDivisor (st N).Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (y N) hN
    with hEW
  have hEWg : EW.genericPoint = y N := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  refine ⟨(st N).Y, inferInstance, inferInstance, inferInstance, inferInstance, (st N).q,
    hGN.normal, hGN.bir, EW, hGN.proj, hGN.smooth, ?_, ?_, ?_, hGN.snc, ?_⟩
  · intro P h0 h1 h2
    have := hRN P h0 h1 h2
    rwa [show Mori.PrimeDivisor.genericPoint EW = y N from hEWg]
  · -- `E` appears on the last model
    obtain ⟨D, hDy, hDv⟩ := exists_properDivisorOver_comap_valuation_eq hXv E R
      v.mem_valuationSubring_iff hS (st N).q hGN.normal hGN.bir hdom (st N).g
      (st N).comm
    have hDE := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hGN.normal
      D.toDivisorOver EW (hDy.trans hEWg.symm)
    rw [hv, hDv]
    ext t
    change EW.divisorialValuation (functionFieldMap (st N).q t) =
      D.toDivisorOver.valuation (functionFieldMap (st N).q t)
    rw [hDE]
    change _ = EW.divisorialValuation (functionFieldMap (𝟙 _) (functionFieldMap (st N).q t))
    rw [MMP.Mori.functionFieldMap_id_apply]
  · -- every exceptional prime has log discrepancy zero
    intro F hF
    have hFξ := hGN.apply_genericPoint_eq_of_isExceptional hXv F hF
    have hc := hGN.crep F
    rw [if_pos (by rwa [hFξ])] at hc
    exact isLogDiscrepancy_of_isDiscrepancy_oneDivisor hXv hXs hB1 hK _ hGN.proper hc
      (fun P hP0 hP1 => by
        change (st N).q F.genericPoint ∉ _
        rw [hFξ]; exact hξ₀P P hP0 hP1)
  · -- `ord_F A = 0` at every exceptional prime
    intro A hA0 hAB hAq hA1 hA A' hA' F hF
    have hFξ := hGN.apply_genericPoint_eq_of_isExceptional hXv F hF
    refine hA'.coeff_eq_zero_of_notMem hAq F ?_
    rw [hFξ]
    intro hmem
    obtain ⟨P, hP0, hξP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    have hAP : 0 < A.coeff P := lt_of_le_of_ne (hA0 P) (Ne.symm hP0)
    have hBP : (A.coeff P : ℝ) ≤ B.coeff P := hAB P
    refine hξ₀P P ?_ (hA1 P hP0) hξP
    have : (0 : ℝ) < A.coeff P := by exact_mod_cast hAP
    exact (lt_of_lt_of_le this hBP).ne'

end MMP.Fourfold

end
