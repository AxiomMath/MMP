module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Intersection.CurveCartierLocal
import MMP.AlgebraicGeometry.MMP.Abundance.Curve.AdmissibleSectionsGenerate
import MMP.AlgebraicGeometry.MMP.Fourfold.Preadmissible.CrepantDifferentMatch
import MMP.AlgebraicGeometry.MMP.Fourfold.Preadmissible.ExceptionalFloorResidue

/-!
# Crepant birational maps fix the boundary restrictions of preadmissible surface sections

Let `(X_i, B_i)` be a finite collection of effective normal projective rational dlt surface
pairs, and let `m` be even and divisible enough that every iterated stratum adjoint is Cartier
(`MMP.Fourfold.IsStratifiedSectionSetting`). Take a preadmissible section system
`s = (s_i) ∈ ⊕ᵢ H⁰(X_i, m(K_{X_i} + B_i))` (`MMP.Fourfold.preadmissibleSections`) and a crepant
birational map `φ : (X_i, B_i) ⇢ (X_j, B_j)` (`MMP.Fourfold.IsCrepantBirationalMap`), possibly
with `i = j`. Then:

* replacing the `i`-th entry of `s` by the pluriform pull-back `φ^* s_j` gives a preadmissible
  system again;
* `φ^* s_j` has the same residue restrictions as `s_i` on every proper stratum of `X_i`, that is,
  on the components of the reduced floor `⌊B_i⌋` and on their intersection points.

For `i = j` this says that crepant birational self-maps of `(X_i, B_i)` preserve the
preadmissible space and act trivially on its restrictions to the reduced floor.

## Main results

* `MMP.Fourfold.ResidueRestriction.exists_preadmissible_pluriformPullback_and_toFun_eq`

## Implementation notes

The proof passes to log resolutions that are isomorphisms at the generic points of all lc strata,
factors a common resolution into point blowups, and uses that a new coefficient-one curve
appears only over a crossing of two floor curves. On such a chain the adjoint has degree zero,
and its even pluriform sections are detected by their residue at an end point.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold
open MMP.Threefold.Mori.Helpers MMP.Threefold.Mori.ModelIndependence

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace Proof_lem_fourfold_surface_preadmissible_boundary_fixed

variable {k : Type} [Field k] {I : Type*} {X : I → Scheme.{0}} {sX : ∀ i, X i ⟶ Spec (.of k)}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    {B : ∀ i, QDivisor (X i)} {m : ℕ}

/-- The zero form has residue zero along an adjunction step. -/
private theorem isPoincareResidue_zero {k : Type} [Field k] [PerfectField k] {Y T : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T]
    [LocallyOfFiniteType sY] {j : T ⟶ Y} {BY : QDivisor Y} {BT : QDivisor T}
    (hj : IsAdjunctionStep sY BY j BT) {e m : ℕ} :
    IsPoincareResidue sY j e m 0 0 := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  obtain ⟨hdvr, -, -, -, hcoh, -⟩ := hj.stalk_facts
  obtain ⟨ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk (j (genericPoint T)))
  have h0 : algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  refine ⟨ϖ, 0, 0, (Scheme.ord_eq_iff hcoh h0).mpr (Ring.ordFrac_irreducible hϖ), ?_, ?_⟩ <;>
    simp <;> rfl

/-- **Residues vanishing along first steps vanish along all proper strata.** If a section `w`
of `m(K_{X_i} + B_i)` has residue restriction zero along every flag of length one, then every
iterated residue of `w` along a flag of positive length is zero. -/
private theorem eq_zero_of_isIteratedResidueRec (R : ResidueRestriction sX B 2 m) (i : I)
    (w : logPluricanonicalSections (sX i) 2 m (B i))
    (hw : ∀ {T : Scheme.{0}} {j : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
      (hj : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) j BT) (e : ℕ),
      topologicalKrullDim T = e → R.toFun i (.step (.refl h) j BT hj) e w = 0)
    {S : Scheme.{0}} {ι : S ⟶ X i} {BS : QDivisor S}
    (F : StratumAdjunctionData (sX i) (B i) ι BS) (hF : 0 < F.length) {e : ℕ}
    {ρ : @RationalPluriForms k _ S (ι ≫ sX i) F.isIntegral_stratum e m}
    (hρ : IsIteratedResidueRec (w : RationalPluriForms (sX i) 2 m) F e ρ) : ρ = 0 := by
  have hP := R.setting.isPair i
  have := hP.charZero
  induction F generalizing e with
  | refl h => simp [StratumAdjunctionData.length] at hF
  | @step S T ι BS F j BT hj ih =>
    obtain ⟨ρ₀, h₀, ρ', hr, hρρ⟩ := hρ
    rcases Nat.eq_zero_or_pos F.length with h0 | h0
    · cases F with
      | step => simp [StratumAdjunctionData.length] at h0
      | refl h =>
        haveI : IsIntegral T := hj.1.1.toIsIntegral
        haveI : LocallyOfFiniteType (j ≫ 𝟙 (X i) ≫ sX i) := hj.1.1.toLocallyOfFiniteType
        have hne := h₀.1
        have hT := topologicalKrullDim_eq_toNat_trdeg (j ≫ 𝟙 (X i) ≫ sX i)
        have hdl := StratumAdjunctionData.dim_add_length (R.setting.topologicalKrullDim_eq i)
          (StratumAdjunctionData.step (.refl h) j BT hj) hT
        simp only [StratumAdjunctionData.length] at hdl
        have hdim : topologicalKrullDim T = e := by
          rw [hT]
          exact_mod_cast (by omega : _ = e)
        have key := (R.isIteratedResidue i (.step (.refl h) j BT hj) e w hdim).rec'
        have hρ : IsIteratedResidueRec (w : RationalPluriForms (sX i) 2 m)
            (StratumAdjunctionData.step (.refl h) j BT hj) e ρ := ⟨ρ₀, h₀, ρ', hr, hρρ⟩
        have hu := IsIteratedResidueRec.unique _ hρ key
        rw [hu, hw h hj e hdim]
    · haveI := F.isIntegral_stratum
      haveI := F.isNormal_stratum
      haveI := F.isLocallyNoetherian_stratum
      haveI : IsIntegral T := hj.1.1.toIsIntegral
      haveI : LocallyOfFiniteType (ι ≫ sX i) := F.isNormalVariety.1.toLocallyOfFiniteType
      obtain rfl := ih h0 h₀
      obtain rfl := IsPoincareResidue.unique hj hr (isPoincareResidue_zero hj)
      exact eq_of_heq hρρ

/-- **Local rings along matched prime divisors.** If `σ : k(X') ≅ k(X)` carries the valuation
of the prime divisor `Γ` of `X` to that of the prime divisor `Γ'` of `X'`, it restricts to an
isomorphism `𝒪_{X',Γ'} ≅ 𝒪_{X,Γ}` preserving orders. -/
private theorem exists_stalk_ringHom_of_divisorialValuation_eq {k : Type} [Field k]
    {X X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} (σ : FunctionFieldEquiv sX sX')
    (Γ : MMP.Mori.PrimeDivisor X) (Γ' : MMP.Mori.PrimeDivisor X')
    (hv : ∀ g, Γ'.divisorialValuation g = Γ.divisorialValuation ((σ.toHom) g))
    {x : X} {x' : X'} (hx : x = Γ.genericPoint) (hx' : x' = Γ'.genericPoint) :
    ∃ ψ : X'.presheaf.stalk x' →+* X.presheaf.stalk x, Function.Bijective ψ ∧
      (∀ a, algebraMap _ X.functionField (ψ a) = (σ.toHom) (algebraMap _ X'.functionField a)) ∧
      ∀ a, X.ord (algebraMap _ X.functionField (ψ a)) x =
        X'.ord (algebraMap _ X'.functionField a) x' := by
  subst hx hx'
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let φ : X'.functionField →+* X.functionField := (σ.toHom).toRingHom
  have h12 : ∀ a1 : Γ'.localRing, ∃ a2 : Γ.localRing,
      algebraMap Γ.localRing X.functionField a2 =
        φ (algebraMap Γ'.localRing X'.functionField a1) := by
    intro a1
    have : Γ'.divisorialValuation (algebraMap Γ'.localRing X'.functionField a1) ≤ 1 :=
      (Γ'.divisorialValuation_le_one_iff _).mpr ⟨a1, rfl⟩
    rw [hv] at this
    exact (Γ.divisorialValuation_le_one_iff _).mp this
  have h21 : ∀ a2 : Γ.localRing, ∃ a1 : Γ'.localRing,
      φ (algebraMap Γ'.localRing X'.functionField a1) =
        algebraMap Γ.localRing X.functionField a2 := by
    intro a2
    obtain ⟨y, hy⟩ := σ.surjective (algebraMap Γ.localRing X.functionField a2)
    have : Γ'.divisorialValuation y ≤ 1 := by
      rw [hv]
      change Γ.divisorialValuation (σ y) ≤ 1
      rw [hy]
      exact (Γ.divisorialValuation_le_one_iff _).mpr ⟨a2, rfl⟩
    obtain ⟨a1, ha1⟩ := (Γ'.divisorialValuation_le_one_iff _).mp this
    exact ⟨a1, by rwa [ha1]⟩
  obtain ⟨ψ, hψb, hψ⟩ := exists_ringHom_bijective_of_range φ h12 h21
  refine ⟨ψ, hψb, hψ, fun a => ?_⟩
  by_cases ha : algebraMap Γ'.localRing X'.functionField a = 0
  · have : algebraMap Γ.localRing X.functionField (ψ a) = 0 := by
      rw [hψ]
      change φ _ = 0
      rw [ha, map_zero]
    rw [this, ha]
    simp [Scheme.ord_zero]
  · have hb : algebraMap Γ.localRing X.functionField (ψ a) ≠ 0 := by
      rw [hψ]
      exact (map_ne_zero φ).mpr ha
    have h1 := hv (algebraMap Γ'.localRing X'.functionField a)
    change _ = Γ.divisorialValuation (φ _) at h1
    rw [← hψ, Γ.divisorialValuation_eq_exp_neg_ord hb,
      Γ'.divisorialValuation_eq_exp_neg_ord ha, WithZero.exp_inj] at h1
    exact (neg_inj.mp h1).symm

/-- **Function fields of matched divisors.** Let `ι : T ⟶ X`, `ι' : T' ⟶ X'` be closed
immersions of integral schemes over `k`, and `ψ : 𝒪_{X',ι'(η_{T'})} ≅ 𝒪_{X,ι(η_T)}` a
`k`-isomorphism of the local rings at the images of the generic points. Then `ψ` induces a
`k`-isomorphism `k(T') ≅ k(T)` of the residue fields, compatible with the restriction maps. -/
private theorem exists_functionFieldEquiv_of_stalk_ringHom {k : Type} [Field k]
    {X X' T T' : Scheme.{0}} [IsIntegral T] [IsIntegral T'] {sX : X ⟶ Spec (.of k)}
    {sX' : X' ⟶ Spec (.of k)} (ι : T ⟶ X) (ι' : T' ⟶ X') [IsClosedImmersion ι]
    [IsClosedImmersion ι']
    (ψ : X'.presheaf.stalk (ι' (genericPoint T')) →+* X.presheaf.stalk (ι (genericPoint T)))
    (hψb : Function.Bijective ψ)
    (hψk : ∀ c : k, ψ (letI := stalkAlgebra sX' (ι' (genericPoint T')); algebraMap k _ c) =
      (letI := stalkAlgebra sX (ι (genericPoint T)); algebraMap k _ c)) :
    ∃ σT : FunctionFieldEquiv (ι ≫ sX) (ι' ≫ sX'),
      ∀ a, (ι.stalkMap (genericPoint T)).hom (ψ a) =
        (σT.toHom) ((ι'.stalkMap (genericPoint T')).hom a) := by
  let := functionFieldAlgebra (ι ≫ sX)
  let := functionFieldAlgebra (ι' ≫ sX')
  set π := (ι.stalkMap (genericPoint T)).hom
  set π' := (ι'.stalkMap (genericPoint T')).hom
  have hπ : Function.Surjective π := ι.stalkMap_surjective _
  have hπ' : Function.Surjective π' := ι'.stalkMap_surjective _
  have hπψ : Function.Surjective (π.comp ψ) := hπ.comp hψb.2
  have hker : RingHom.ker π' = RingHom.ker (π.comp ψ) := by
    rw [IsLocalRing.ker_eq_maximalIdeal π' hπ',
      IsLocalRing.ker_eq_maximalIdeal (π.comp ψ) hπψ]
  let eT : T'.functionField ≃+* T.functionField :=
    (RingHom.quotientKerEquivOfSurjective hπ').symm.trans
      ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hπψ))
  have heT : ∀ a, eT (π' a) = π (ψ a) := by
    intro a
    have h1 : (RingHom.quotientKerEquivOfSurjective hπ').symm (π' a) =
        Ideal.Quotient.mk _ a := by
      rw [RingEquiv.symm_apply_eq]; rfl
    change (RingHom.quotientKerEquivOfSurjective hπψ)
      ((Ideal.quotEquivOfEq hker) ((RingHom.quotientKerEquivOfSurjective hπ').symm (π' a))) = _
    rw [h1]
    rfl
  refine ⟨AlgEquiv.ofRingEquiv (f := eT) fun c => ?_, fun a => (heT a).symm⟩
  have e1 := MMP.Threefold.Resolution.stalkMap_algebraMap (sX := sX') ι' (genericPoint T') c
  have e2 := MMP.Threefold.Resolution.stalkMap_algebraMap (sX := sX) ι (genericPoint T) c
  change eT (algebraMap k (T'.presheaf.stalk (genericPoint T')) c) =
    algebraMap k (T.presheaf.stalk (genericPoint T)) c
  rw [← e1, ← e2]
  change eT (π' _) = π _
  rw [heT, hψk]

/-- A crepant birational map matching two prime divisors matches their boundary coefficients. -/
private theorem coeff_eq_of_divisorialValuation_eq (R : ResidueRestriction sX B 2 m) {i j : I}
    (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ) (P : MMP.Mori.PrimeDivisor (X i))
    (P' : MMP.Mori.PrimeDivisor (X j))
    (hP' : ∀ g, P'.divisorialValuation g = P.divisorialValuation ((σ.toHom) g)) :
    (B j).coeff P' = (B i).coeff P := by
  have hPi := R.setting.isPair i
  have hPj := R.setting.isPair j
  haveI := hPi.isAlgClosed
  haveI := hPi.charZero
  have hX := hPi.isPair.isNormalVariety
  have hXj := hPj.isPair.isNormalVariety
  obtain ⟨d, K, hK, -⟩ := R.setting.isCartierDivisor i (.refl hPi.isPair)
  obtain ⟨d', K', hK', -⟩ := R.setting.isCartierDivisor j (.refl hPj.isPair)
  rw [Category.id_comp] at hK hK'
  set DΓ := DivisorOver.ofPrimeDivisor k hX P
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPi.isPair hK DΓ
  have hc' : c = -(B i).coeff P := hc.eq_neg_coeff_of_ofPrimeDivisor hX
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (show IsProper (𝟙 (X i)) by infer_instance)
  obtain ⟨n', D, hDv, hDlog⟩ := (hσ DΓ.valuation (1 + c)).mp ⟨d, DΓ, rfl, hlog⟩
  set DΓ' := DivisorOver.ofPrimeDivisor k hXj P'
  obtain ⟨c₂, hc₂⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPj.isPair hK' DΓ'
  have hc₂' : c₂ = -(B j).coeff P' := hc₂.eq_neg_coeff_of_ofPrimeDivisor hXj
  have hlog' := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc₂
    (show IsProper (𝟙 (X j)) by infer_instance)
  have hv : D.valuation = DΓ'.valuation := by
    ext g
    rw [hDv]
    change P.divisorialValuation (functionFieldMap (𝟙 (X i)) _) =
      P'.divisorialValuation (functionFieldMap (𝟙 (X j)) g)
    rw [functionFieldMap_id_apply, functionFieldMap_id_apply, hP']
    rfl
  have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hDlog hlog' hv
  have h2 : ((c : ℚ) : ℝ) = ((c₂ : ℚ) : ℝ) := by linarith
  have h3 : c = c₂ := by exact_mod_cast h2
  rw [hc', hc₂'] at h3
  linarith

/-- A floor curve of a component is the final stratum of a flag of positive length. -/
private theorem exists_stratumAdjunctionData_of_one_le_coeff (R : ResidueRestriction sX B 2 m)
    (l : I) (P : MMP.Mori.PrimeDivisor (X l)) (hP : 1 ≤ (B l).coeff P) :
    ∃ (T : Scheme.{0}) (ι : T ⟶ X l) (BT : QDivisor T)
      (F : StratumAdjunctionData (sX l) (B l) ι BT),
      Set.range ι.base = (P.support : Set (X l)) ∧ 0 < F.length := by
  have hPl := R.setting.isPair l
  haveI := hPl.isAlgClosed
  haveI := hPl.charZero
  have hinter : (⋂ Q ∈ ({P} : Finset (MMP.Mori.PrimeDivisor (X l))), (Q.support : Set (X l))) =
      P.support := by simp
  have hS : IsDltStratum (sX l) (B l) (P.support : Set (X l)) := by
    refine ⟨R.setting.isDltPair l, {P}, Finset.singleton_nonempty _, by simpa using hP, ?_, ?_⟩
    · rw [hinter]
      exact ⟨P.genericPoint, by
        rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩
    · rw [hinter]
      refine ⟨⟨?_, le_rfl⟩, fun T hT _ => hT.2⟩
      rw [PrimeDivisor.support_eq_closure]
      exact isIrreducible_singleton.closure
  obtain ⟨T, ι, BT, hrange, ⟨F⟩⟩ := hS.exists_isStratumAdjunctionPair_and_isDltPair.1.1
  refine ⟨T, ι, BT, F, hrange, ?_⟩
  cases F with
  | refl h =>
    exfalso
    have h1 : genericPoint (X l) ∈ Set.range (𝟙 (X l) : X l ⟶ X l).base := ⟨_, rfl⟩
    rw [hrange] at h1
    exact MMP.Threefold.Mori.OpenRestriction.genericPoint_notMem_support P h1
  | step F j BT hj => simp [StratumAdjunctionData.length]

/-- A closed immersion of an integral scheme onto the support of a prime divisor sends the generic
point to the generic point of the divisor. -/
private theorem genericPoint_eq_of_range_eq {Y T : Scheme.{0}} [IsIntegral T] (j : T ⟶ Y)
    [IsClosedImmersion j] (P : MMP.Mori.PrimeDivisor Y)
    (hrange : Set.range j.base = (P.support : Set Y)) : j (genericPoint T) = P.genericPoint := by
  have h1 : closure ({j (genericPoint T)} : Set Y) = Set.range j.base := by
    apply le_antisymm
    · rw [hrange]
      exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure P ▸
        isClosed_closure).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr (hrange ▸ Set.mem_range_self _))
    · rintro _ ⟨z, rfl⟩
      have hz : genericPoint T ⤳ z := (genericPoint_spec T).specializes trivial
      exact specializes_iff_mem_closure.mp (hz.map j.continuous)
  have h2 : closure ({j (genericPoint T)} : Set Y) = closure {P.genericPoint} := by
    rw [h1, hrange, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact (inseparable_iff_closure_eq.mpr h2).eq

/-- The stratum of an adjunction step lies on a prime divisor with coefficient at least one. -/
private theorem one_le_coeff_of_isAdjunctionStep {k : Type} [Field k] {Y T : Scheme.{0}}
    [IsIntegral T] {sY : Y ⟶ Spec (.of k)} {BY : QDivisor Y} {j : T ⟶ Y} {BT : QDivisor T}
    (hj : IsAdjunctionStep sY BY j BT) (P : MMP.Mori.PrimeDivisor Y)
    (hP : j (genericPoint T) = P.genericPoint) : 1 ≤ BY.coeff P := by
  obtain ⟨-, P₀, h1, hrange, hci, -⟩ := hj
  have h := genericPoint_eq_of_range_eq j P₀ hrange
  rw [hP] at h
  rwa [← AlgebraicGeometry.PrimeDivisor.genericPoint_injective h] at h1

/-- A closed integral subscheme of a component supported on a prime divisor is a curve. -/
private theorem topologicalKrullDim_eq_one_of_range_eq (R : ResidueRestriction sX B 2 m) (l : I)
    {T : Scheme.{0}} [IsIntegral T] (ι : T ⟶ X l) [IsClosedImmersion ι]
    [LocallyOfFiniteType (ι ≫ sX l)] (P : MMP.Mori.PrimeDivisor (X l))
    (hrange : Set.range ι.base = (P.support : Set (X l))) :
    topologicalKrullDim T = (1 : ℕ) := by
  have hPl := R.setting.isPair l
  haveI := hPl.isAlgClosed
  haveI := hPl.charZero
  have hX := hPl.isPair.isNormalVariety
  haveI : LocallyOfFiniteType (sX l) := hX.1.toLocallyOfFiniteType
  have h1 := trdeg_add_one_of_eq_genericPoint (sY := sX l) P
    (genericPoint_eq_of_range_eq ι P hrange)
  have h2 := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX l)
    (R.setting.topologicalKrullDim_eq l)
  rw [topologicalKrullDim_eq_toNat_trdeg (ι ≫ sX l)]
  congr 1
  omega

/-- **Crepancy of a birational map of curve pairs from matching points.** Let `σ : k(C') ≅ k(C)`
be a `k`-isomorphism of function fields of normal curve pairs `(C, B)`, `(C', B')` such that
`σ` matches the points of `C` and `C'` (`ord_Q ∘ σ = ord_{Q'}`) together with their boundary
coefficients, in both directions. Then `σ` is crepant. -/
private theorem isCrepantBirationalMap_of_curve {k : Type} [Field k] [IsAlgClosed k]
    {C C' : Scheme.{0}} {sC : C ⟶ Spec (.of k)} {sC' : C' ⟶ Spec (.of k)} [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] [IsIntegral C'] [IsLocallyNoetherian C'] [IsNormal C']
    (hvar : IsNormalVariety k sC) (hvar' : IsNormalVariety k sC')
    (hdim : topologicalKrullDim C = 1) (hdim' : topologicalKrullDim C' = 1)
    {B : QDivisor C} {B' : QDivisor C'} (hpair : MMP.Mori.IsPair sC B)
    (hpair' : MMP.Mori.IsPair sC' B') (σ : FunctionFieldEquiv sC sC')
    (h₁ : ∀ Q : MMP.Mori.PrimeDivisor C, ∃ Q' : MMP.Mori.PrimeDivisor C',
      (∀ f, f ≠ 0 → C.ord ((σ.toHom) f) Q.genericPoint = C'.ord f Q'.genericPoint) ∧
        B.coeff Q = B'.coeff Q')
    (h₂ : ∀ Q' : MMP.Mori.PrimeDivisor C', ∃ Q : MMP.Mori.PrimeDivisor C,
      (∀ f, f ≠ 0 → C.ord ((σ.toHom) f) Q.genericPoint = C'.ord f Q'.genericPoint) ∧
        B.coeff Q = B'.coeff Q') :
    IsCrepantBirationalMap sC sC' B B' σ := by
  let := functionFieldAlgebra sC
  let := functionFieldAlgebra sC'
  intro v a
  rw [hasLogDiscrepancy_iff_of_curve hvar hdim hpair,
    hasLogDiscrepancy_iff_of_curve hvar' hdim' hpair']
  constructor
  · rintro ⟨Q, rfl, rfl⟩
    obtain ⟨Q', hQ', hc⟩ := h₁ Q
    refine ⟨Q', ?_, by rw [hc]⟩
    ext f
    by_cases hf : f = 0
    · subst hf
      simp
    have hσf : (σ.toHom) f ≠ 0 := (map_ne_zero _).mpr hf
    change (DivisorOver.ofPrimeDivisor k hvar Q).valuation ((σ.toHom) f) = _
    rw [valuation_ofPrimeDivisor_apply hvar Q hσf, valuation_ofPrimeDivisor_apply hvar' Q' hf,
      hQ' f hf]
  · rintro ⟨Q', hv, rfl⟩
    obtain ⟨Q, hQ, hc⟩ := h₂ Q'
    refine ⟨Q, ?_, by rw [hc]⟩
    ext g
    obtain ⟨f, rfl⟩ := σ.surjective g
    by_cases hf : f = 0
    · subst hf
      simp
    have hσf : (σ.toHom) f ≠ 0 := (map_ne_zero _).mpr hf
    have := congrArg (fun w => w f) hv
    change v ((σ.toHom) f) = _ at this
    change v ((σ.toHom) f) = _
    rw [this, valuation_ofPrimeDivisor_apply hvar' Q' hf, ← hQ f hf]
    exact (valuation_ofPrimeDivisor_apply hvar Q hσf).symm

/-- **The induced map of floor curves is crepant.** Let `σ` be a crepant birational map
`(X_i, B_i) ⇢ (X_j, B_j)` carrying the valuation of the floor curve `P ⊆ X_i` to that of the
floor curve `P' ⊆ X_j`, `T ⟶ X_i` and `T' ⟶ X_j` the normal curves over `P` and `P'` with
their differents `B_T` and `B_{T'}`, and `σ_T : k(T') ≅ k(T)` the isomorphism of residue fields
induced by `σ`. Then `σ_T : (T, B_T) ⇢ (T', B_{T'})` is crepant. -/
private theorem isCrepantBirationalMap_residue (R : ResidueRestriction sX B 2 m) {i j : I}
    (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {T T' : Scheme.{0}} [IsIntegral T] [IsIntegral T'] {ι : T ⟶ X i} {ι' : T' ⟶ X j}
    {BT : QDivisor T} {BT' : QDivisor T'} (h : MMP.Mori.IsPair (sX i) (B i))
    (h' : MMP.Mori.IsPair (sX j) (B j))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT)
    (hι' : IsAdjunctionStep (𝟙 (X j) ≫ sX j) (B j) ι' BT')
    (P : MMP.Mori.PrimeDivisor (X i)) (hP : ι (genericPoint T) = P.genericPoint)
    (P' : MMP.Mori.PrimeDivisor (X j)) (hP'g : ι' (genericPoint T') = P'.genericPoint)
    (hP' : ∀ g, P'.divisorialValuation g = P.divisorialValuation ((σ.toHom) g))
    (ψ : (X j).presheaf.stalk (ι' (genericPoint T')) →+* (X i).presheaf.stalk (ι (genericPoint T)))
    (hψ : ∀ a, algebraMap _ (X i).functionField (ψ a) =
      (σ.toHom) (algebraMap _ (X j).functionField a))
    (σT : FunctionFieldEquiv ((ι ≫ 𝟙 (X i)) ≫ sX i) ((ι' ≫ 𝟙 (X j)) ≫ sX j))
    (hσT : ∀ a, (ι.stalkMap (genericPoint T)).hom (ψ a) =
      (σT.toHom) ((ι'.stalkMap (genericPoint T')).hom a)) :
    haveI := (StratumAdjunctionData.step (.refl h) ι BT hι).isNormal_stratum
    haveI := (StratumAdjunctionData.step (.refl h) ι BT hι).isLocallyNoetherian_stratum
    haveI := (StratumAdjunctionData.step (.refl h') ι' BT' hι').isNormal_stratum
    haveI := (StratumAdjunctionData.step (.refl h') ι' BT' hι').isLocallyNoetherian_stratum
    IsCrepantBirationalMap ((ι ≫ 𝟙 (X i)) ≫ sX i) ((ι' ≫ 𝟙 (X j)) ≫ sX j) BT BT' σT := by
  have hPi := R.setting.isPair i
  haveI := hPi.isAlgClosed
  haveI := hPi.charZero
  set F := StratumAdjunctionData.step (.refl h) ι BT hι with hF
  set F' := StratumAdjunctionData.step (.refl h') ι' BT' hι' with hF'
  haveI := F.isNormal_stratum
  haveI := F.isLocallyNoetherian_stratum
  haveI := F'.isNormal_stratum
  haveI := F'.isLocallyNoetherian_stratum
  have hvar : IsNormalVariety k ((ι ≫ 𝟙 (X i)) ≫ sX i) := F.isNormalVariety
  have hvar' : IsNormalVariety k ((ι' ≫ 𝟙 (X j)) ≫ sX j) := F'.isNormalVariety
  haveI : LocallyOfFiniteType ((ι ≫ 𝟙 (X i)) ≫ sX i) := hvar.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType ((ι' ≫ 𝟙 (X j)) ≫ sX j) := hvar'.1.toLocallyOfFiniteType
  have hdim : topologicalKrullDim T = (1 : ℕ) := by
    have hT := topologicalKrullDim_eq_toNat_trdeg ((ι ≫ 𝟙 (X i)) ≫ sX i)
    have hdl := StratumAdjunctionData.dim_add_length (R.setting.topologicalKrullDim_eq i) F hT
    simp only [hF, StratumAdjunctionData.length] at hdl
    rw [hT]
    exact_mod_cast (by omega : _ = 1)
  have hdim' : topologicalKrullDim T' = (1 : ℕ) := by
    have hT := topologicalKrullDim_eq_toNat_trdeg ((ι' ≫ 𝟙 (X j)) ≫ sX j)
    have hdl := StratumAdjunctionData.dim_add_length (R.setting.topologicalKrullDim_eq j) F' hT
    simp only [hF', StratumAdjunctionData.length] at hdl
    rw [hT]
    exact_mod_cast (by omega : _ = 1)
  have hpair : MMP.Mori.IsPair ((ι ≫ 𝟙 (X i)) ≫ sX i) BT := by
    obtain ⟨d, K, hK, hC⟩ := R.setting.isCartierDivisor i F
    exact ⟨hvar, d, K, hK, m, by exact_mod_cast R.setting.pos.ne', hC⟩
  have hpair' : MMP.Mori.IsPair ((ι' ≫ 𝟙 (X j)) ≫ sX j) BT' := by
    obtain ⟨d, K, hK, hC⟩ := R.setting.isCartierDivisor j F'
    exact ⟨hvar', d, K, hK, m, by exact_mod_cast R.setting.pos.ne', hC⟩
  obtain ⟨h₁, h₂⟩ := exists_primeDivisor_coeff_eq_residue_of_isCrepantBirationalMap R σ hσ h h'
    hι hι' P hP P' hP'g hP' ψ hψ σT hσT
  exact isCrepantBirationalMap_of_curve hvar hvar' (by exact_mod_cast hdim)
    (by exact_mod_cast hdim') hpair hpair' σT h₁ h₂

/-- The floor-curve comparison when `σ` carries the valuation of the floor curve `P ⊆ X_i` to
the valuation of a prime divisor `P'` of `X_j`. -/
private theorem toFun_step_refl_eq_of_divisorialValuation_eq (R : ResidueRestriction sX B 2 m)
    {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {s : ∀ l, logPluricanonicalSections (sX l) 2 m (B l)} (hs : s ∈ preadmissibleSections R)
    (u : logPluricanonicalSections (sX i) 2 m (B i))
    (hu : (u : RationalPluriForms (sX i) 2 m) =
        pluriformPullback (sX i) (sX j) σ.toHom 2 m (s j))
    {T : Scheme.{0}} [IsIntegral T] {ι : T ⟶ X i} {BT : QDivisor T}
    (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) (e : ℕ)
    (he : topologicalKrullDim T = e) (P : MMP.Mori.PrimeDivisor (X i))
    (hP : ι (genericPoint T) = P.genericPoint) (P' : MMP.Mori.PrimeDivisor (X j))
    (hP' : ∀ g, P'.divisorialValuation g = P.divisorialValuation ((σ.toHom) g)) :
    R.toFun i (.step (.refl h) ι BT hι) e u = R.toFun i (.step (.refl h) ι BT hι) e (s i) := by
  have hPi := R.setting.isPair i
  have hPj := R.setting.isPair j
  haveI := hPi.isAlgClosed
  haveI := hPi.charZero
  have hXi := hPi.isPair.isNormalVariety
  have hXj := hPj.isPair.isNormalVariety
  haveI : LocallyOfFiniteType (sX i) := hXi.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (sX j) := hXj.1.toLocallyOfFiniteType
  -- the flag on `X_j` ending at `P'`
  have hcP : 1 ≤ (B i).coeff P := one_le_coeff_of_isAdjunctionStep hι P hP
  have hcP' : 1 ≤ (B j).coeff P' := by
    rwa [coeff_eq_of_divisorialValuation_eq R σ hσ P P' hP']
  obtain ⟨T', ι₀, BT', F', hrange', hlen'⟩ :=
    exists_stratumAdjunctionData_of_one_le_coeff R j P' hcP'
  haveI := F'.isIntegral_stratum
  haveI : IsClosedImmersion ι₀ := F'.isClosedImmersion
  haveI : LocallyOfFiniteType (ι₀ ≫ sX j) := F'.isNormalVariety.1.toLocallyOfFiniteType
  have hdim' := topologicalKrullDim_eq_one_of_range_eq R j ι₀ P' hrange'
  have hlen := StratumAdjunctionData.dim_add_length (R.setting.topologicalKrullDim_eq j) F' hdim'
  have he1 : e = 1 := by
    have := StratumAdjunctionData.dim_add_length (R.setting.topologicalKrullDim_eq i)
      (StratumAdjunctionData.step (.refl h) ι BT hι) he
    simp only [StratumAdjunctionData.length] at this
    omega
  subst he1
  cases F' with
  | refl h₀ => simp [StratumAdjunctionData.length] at hlen'
  | step F'' ι' BT'' hι' =>
    cases F'' with
    | step F₃ _ _ _ =>
      simp only [StratumAdjunctionData.length] at hlen
      omega
    | refl h' =>
    obtain ⟨-, -, hιc⟩ := hι.exists_primeDivisor
    obtain ⟨-, -, hιc'⟩ := hι'.exists_primeDivisor
    haveI := hιc
    haveI := hιc'
    have hP'g : ι' (genericPoint T') = P'.genericPoint := genericPoint_eq_of_range_eq ι' P' hrange'
    obtain ⟨ψ, hψb, hψ, hord⟩ :=
      exists_stalk_ringHom_of_divisorialValuation_eq σ P P' hP' hP hP'g
    have hψk : ∀ c : k,
        ψ (letI := stalkAlgebra (𝟙 (X j) ≫ sX j) (ι' (genericPoint T')); algebraMap k _ c) =
          (letI := stalkAlgebra (𝟙 (X i) ≫ sX i) (ι (genericPoint T)); algebraMap k _ c) := by
      intro c
      let := stalkAlgebra (sX j) (ι' (genericPoint T'))
      let := stalkAlgebra (sX i) (ι (genericPoint T))
      let := functionFieldAlgebra (sX j)
      let := functionFieldAlgebra (sX i)
      haveI := isScalarTower_stalk_functionField (sX j) (ι' (genericPoint T'))
      haveI := isScalarTower_stalk_functionField (sX i) (ι (genericPoint T))
      apply IsFractionRing.injective ((X i).presheaf.stalk (ι (genericPoint T))) (X i).functionField
      change algebraMap _ (X i).functionField (ψ (algebraMap k _ c)) =
        algebraMap _ (X i).functionField (algebraMap k _ c)
      rw [hψ, ← IsScalarTower.algebraMap_apply]
      have t := isScalarTower_stalk_functionField (sX i) (ι (genericPoint T))
      exact ((σ.toHom).commutes c).trans (@IsScalarTower.algebraMap_apply k
        ((X i).presheaf.stalk (ι (genericPoint T))) (X i).functionField _ _ _ _ _ _ t c)
    obtain ⟨σT, hσT⟩ := exists_functionFieldEquiv_of_stalk_ringHom (sX := 𝟙 (X i) ≫ sX i)
      (sX' := 𝟙 (X j) ≫ sX j) ι ι' ψ hψb hψk
    have hcrep := isCrepantBirationalMap_residue R σ hσ h h' hι hι' P hP P' hP'g hP' ψ hψ σT hσT
    have hpre := hs i j (StratumAdjunctionData.step (.refl h) ι BT hι)
      (StratumAdjunctionData.step (.refl h') ι' BT' hι') 1 (by simp [StratumAdjunctionData.length])
      (by simp [StratumAdjunctionData.length]) he hdim' σT hcrep
    rw [← hpre]
    haveI : LocallyOfFiniteType (𝟙 (X i) ≫ sX i) := by
      rw [Category.id_comp]
      infer_instance
    haveI : LocallyOfFiniteType (𝟙 (X j) ≫ sX j) := by
      rw [Category.id_comp]
      infer_instance
    haveI : LocallyOfFiniteType (ι ≫ 𝟙 (X i) ≫ sX i) := hι.1.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (ι' ≫ 𝟙 (X j) ≫ sX j) := hι'.1.1.toLocallyOfFiniteType
    obtain ⟨ρ0, ⟨-, h0⟩, ρ', hr, hρ⟩ :=
      (R.isIteratedResidue j (.step (.refl h') ι' BT' hι') 1 (s j) hdim').rec'
    have e0 : ρ0 = (s j : RationalPluriForms (sX j) 2 m) := eq_of_heq h0
    have e1 : R.toFun j (.step (.refl h') ι' BT' hι') 1 (s j) = ρ' := eq_of_heq hρ
    have hdi : topologicalKrullDim (X i) = ((1 + 1 : ℕ) : WithBot ℕ∞) :=
      R.setting.topologicalKrullDim_eq i
    have hdj : topologicalKrullDim (X j) = ((1 + 1 : ℕ) : WithBot ℕ∞) :=
      R.setting.topologicalKrullDim_eq j
    have hres := isPoincareResidue_pluriformPullback (sX := 𝟙 (X i) ≫ sX i)
      (sX' := 𝟙 (X j) ≫ sX j) ι ι' (n := 1) hdi hdj he hdim' σ.toHom σT.toHom ψ hψ hσT hord hr
    have key : IsIteratedResidue (sX i) (B i) (u : RationalPluriForms (sX i) 2 m)
        (.step (.refl h) ι BT hι) 1
        (pluriformPullback ((ι ≫ 𝟙 (X i)) ≫ sX i) ((ι' ≫ 𝟙 (X j)) ≫ sX j) σT.toHom 1 m
          (R.toFun j (.step (.refl h') ι' BT' hι') 1 (s j))) := by
      refine IsIteratedResidue.of_rec _ ⟨_, ⟨rfl, heq_of_eq ?_⟩, _, hres, ?_⟩
      · rw [hu, e0]; rfl
      · rw [e1]; exact HEq.rfl
    exact IsIteratedResidue.unique (R.isIteratedResidue i _ 1 u he) key

/-- **Crepant pull-back fixes the residues along the floor curves.** If `s` is preadmissible
and `u = φ^* s_j`, the residues of `u` and of `s_i` along every component of `⌊B_i⌋` agree. -/
private theorem toFun_step_refl_eq (R : ResidueRestriction sX B 2 m)
    {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {s : ∀ l, logPluricanonicalSections (sX l) 2 m (B l)} (hs : s ∈ preadmissibleSections R)
    (u : logPluricanonicalSections (sX i) 2 m (B i))
    (hu : (u : RationalPluriForms (sX i) 2 m) =
        pluriformPullback (sX i) (sX j) σ.toHom 2 m (s j))
    {T : Scheme.{0}} {ι : T ⟶ X i} {BT : QDivisor T} (h : MMP.Mori.IsPair (sX i) (B i))
    (hι : IsAdjunctionStep (𝟙 (X i) ≫ sX i) (B i) ι BT) (e : ℕ)
    (he : topologicalKrullDim T = e) :
    R.toFun i (.step (.refl h) ι BT hι) e u = R.toFun i (.step (.refl h) ι BT hι) e (s i) := by
  have hPi := R.setting.isPair i
  haveI := hPi.isAlgClosed
  haveI := hPi.charZero
  have hX := hPi.isPair.isNormalVariety
  have hXj := (R.setting.isPair j).isPair.isNormalVariety
  obtain ⟨d, K, hK, -⟩ := R.setting.isCartierDivisor i (.refl hPi.isPair)
  rw [Category.id_comp] at hK
  haveI : IsIntegral T := hι.1.1.toIsIntegral
  obtain ⟨P, hP, -⟩ := hι.exists_primeDivisor
  set DΓ := DivisorOver.ofPrimeDivisor k hX P
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPi.isPair hK DΓ
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (show IsProper (𝟙 (X i)) by infer_instance)
  obtain ⟨n', D, hDv, -⟩ := (hσ DΓ.valuation (1 + c)).mp ⟨d, DΓ, rfl, hlog⟩
  have hv : ∀ g, D.valuation g = P.divisorialValuation ((σ.toHom) g) := by
    intro g
    rw [hDv]
    change P.divisorialValuation (functionFieldMap (𝟙 (X i)) _) = _
    rw [functionFieldMap_id_apply]
    rfl
  by_cases hD : D.IsExceptional
  · exact toFun_step_refl_eq_of_isExceptional_of_isCrepantBirationalMap R σ hσ hs u hu h hι e
      he P hP D hv hD
  · obtain ⟨P', hP'⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hXj D hD
    refine toFun_step_refl_eq_of_divisorialValuation_eq R σ hσ hs u hu h hι e he P hP P'
      fun g => ?_
    rw [← hv, hP']
    change _ = P'.divisorialValuation (functionFieldMap (𝟙 (X j)) g)
    rw [functionFieldMap_id_apply]

/-- The residue restrictions of `φ^* s_j` to proper strata of `X_i` are those of `s_i`. -/
private theorem toFun_eq (R : ResidueRestriction sX B 2 m)
    {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {s : ∀ l, logPluricanonicalSections (sX l) 2 m (B l)} (hs : s ∈ preadmissibleSections R)
    (u : logPluricanonicalSections (sX i) 2 m (B i))
    (hu : (u : RationalPluriForms (sX i) 2 m) =
        pluriformPullback (sX i) (sX j) σ.toHom 2 m (s j))
    {S : Scheme.{0}} {ι : S ⟶ X i} {BS : QDivisor S}
    (F : StratumAdjunctionData (sX i) (B i) ι BS) (e : ℕ) (hF : 0 < F.length)
    (he : topologicalKrullDim S = e) : R.toFun i F e u = R.toFun i F e (s i) := by
  haveI := F.isIntegral_stratum
  have hdiff := eq_zero_of_isIteratedResidueRec R i (u - s i)
    (fun h hι e' he' => by
      rw [map_sub, toFun_step_refl_eq R σ hσ hs u hu h hι e' he', sub_self])
    F hF (R.isIteratedResidue i F e (u - s i) he).rec'
  rw [map_sub] at hdiff
  exact sub_eq_zero.mp hdiff

/-- A section system agreeing with a preadmissible one in all residue restrictions to proper
strata is preadmissible. -/
private theorem mem_preadmissibleSections_of_toFun_eq (R : ResidueRestriction sX B 2 m)
    {s t : ∀ l, logPluricanonicalSections (sX l) 2 m (B l)} (hs : s ∈ preadmissibleSections R)
    (h : ∀ (l : I) {S : Scheme.{0}} {ι : S ⟶ X l} {BS : QDivisor S}
      (F : StratumAdjunctionData (sX l) (B l) ι BS) (e : ℕ), 0 < F.length →
        topologicalKrullDim S = e → R.toFun l F e (t l) = R.toFun l F e (s l)) :
    t ∈ preadmissibleSections R := by
  intro i i' S S' ι ι' BS BS' F F' e h₁ h₂ h₃ h₄ σ hσ
  rw [h i F e h₁ h₃, h i' F' e h₂ h₄]
  exact hs i i' F F' e h₁ h₂ h₃ h₄ σ hσ

end Proof_lem_fourfold_surface_preadmissible_boundary_fixed

end

open CategoryTheory AlgebraicGeometry
open MMP.Mori

namespace MMP.Fourfold.ResidueRestriction

/-- **Crepant birational maps fix the floor restrictions of preadmissible surface sections.**
Let `R` be residue restrictions on a finite family of effective normal projective rational dlt
surface pairs `(X_i, B_i)`, in an even degree `m` making every iterated stratum adjoint Cartier.
Let `σ = φ^*` come from a crepant birational map `φ : (X_i, B_i) ⇢ (X_j, B_j)`, where `i = j`
is allowed. Then, for every preadmissible section system `s`:
* the system obtained from `s` by replacing its `i`-th entry with `φ^* s_j` is preadmissible;
* on every proper stratum of `X_i` (flag of positive length), `φ^* s_j` has the same residue
  restriction as `s_i`. -/
@[mmp "lem_fourfold_surface_preadmissible_boundary_fixed"]
public theorem exists_preadmissible_pluriformPullback_and_toFun_eq
    {k : Type} [Field k] {I : Type*} {X : I → Scheme.{0}} {sX : ∀ i, X i ⟶ Spec (.of k)}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    {B : ∀ i, QDivisor (X i)} {m : ℕ} (R : ResidueRestriction sX B 2 m)
    (_hB : ∀ i, 0 ≤ B i) {i j : I} (σ : FunctionFieldEquiv (sX i) (sX j))
    (hσ : IsCrepantBirationalMap (sX i) (sX j) (B i) (B j) σ)
    {s : ∀ l, logPluricanonicalSections (sX l) 2 m (B l)} (hs : s ∈ preadmissibleSections R) :
    (∃ t ∈ preadmissibleSections R,
      ((t i : logPluricanonicalSections (sX i) 2 m (B i)) : RationalPluriForms (sX i) 2 m) =
        pluriformPullback (sX i) (sX j) σ.toHom 2 m (s j) ∧ ∀ l, l ≠ i → t l = s l) ∧
    ∀ u : logPluricanonicalSections (sX i) 2 m (B i),
      (u : RationalPluriForms (sX i) 2 m) =
        pluriformPullback (sX i) (sX j) σ.toHom 2 m (s j) →
      ∀ {S : Scheme.{0}} {ι : S ⟶ X i} {BS : QDivisor S}
        (F : StratumAdjunctionData (sX i) (B i) ι BS) (e : ℕ), 0 < F.length →
        topologicalKrullDim S = e → R.toFun i F e u = R.toFun i F e (s i) := by
  classical
  open Proof_lem_fourfold_surface_preadmissible_boundary_fixed in
  refine ⟨?_, fun u hu S ι BS F e hF he => toFun_eq R σ hσ hs u hu F e hF he⟩
  have hPi := R.setting.isPair i
  have hPj := R.setting.isPair j
  haveI := hPi.isAlgClosed
  haveI := hPi.charZero
  obtain ⟨d', K', hK', hmD'⟩ := R.setting.isCartierDivisor j (.refl hPj.isPair)
  rw [Category.id_comp] at hK'
  obtain rfl : d' = 2 := by
    exact_mod_cast hK'.topologicalKrullDim_eq.symm.trans (R.setting.topologicalKrullDim_eq j)
  let u : logPluricanonicalSections (sX i) 2 m (B i) :=
    ⟨_, pluriformPullback_mem_logPluricanonicalSections_of_isCrepantBirationalMap hPi.isPair
      (R.setting.topologicalKrullDim_eq i) hPj.isPair.isNormalVariety hK' R.setting.pos hmD' hσ
      (s j).2⟩
  refine ⟨Function.update s i u, ?_, by simp [u], fun l hl => Function.update_of_ne hl _ _⟩
  open Proof_lem_fourfold_surface_preadmissible_boundary_fixed in
  refine mem_preadmissibleSections_of_toFun_eq R hs fun l S ι BS F e hF he => ?_
  by_cases hli : l = i
  · subst hli
    rw [Function.update_self]
    exact Proof_lem_fourfold_surface_preadmissible_boundary_fixed.toFun_eq R σ hσ hs u rfl F e hF he
  · rw [Function.update_of_ne hli]

end MMP.Fourfold.ResidueRestriction
